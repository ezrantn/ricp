use crate::interval::Interval;
use fxhash::FxHashMap;

/// Identifier unik untuk variabel (misal "x", "y")
pub type VarId = String;

/// Pemetaan variabel ke domain intervalnya saat ini (Box Region)
pub type BoxRegion = FxHashMap<VarId, Interval>;

pub type NodeId = usize;

/// Jenis operasi matematika di AST node
#[derive(Debug, Clone, PartialEq)]
pub enum OpType {
    Add,
    Sub,
    Mul,
    Div,
    Sqr,
    Sqrt,
    Sin,
    Exp,
    Cos,
}

/// Jenis Node di dalam AST
#[derive(Debug, Clone, PartialEq)]
pub enum NodeKind {
    Constant(f64),
    Variable(VarId),
    Binary {
        op: OpType,
        left: NodeId,
        right: NodeId,
    },
    Unary {
        op: OpType,
        child: NodeId,
    },
}

/// Sebuah Node di AST yang menyimpan state interval sementara
#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    /// Interval evaluasi sementara di node ini (digunakan saat HC4 propagation)
    pub eval_interval: Option<Interval>,
}

/// AST Container berbasis Arena Allocation (`Vec`)
#[derive(Debug, Default, Clone)]
pub struct Ast {
    pub nodes: Vec<Node>,
}

impl Ast {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    /// Menambahkan node Constant
    pub fn add_constant(&mut self, val: f64) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node {
            kind: NodeKind::Constant(val),
            eval_interval: Interval::point(val),
        });
        id
    }

    /// Menambahkan node Variable
    pub fn add_variable(&mut self, name: &str) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node {
            kind: NodeKind::Variable(name.to_string()),
            eval_interval: None,
        });
        id
    }

    /// Menambahkan node Binary Operation (+, -, *, /)
    pub fn add_binary(&mut self, op: OpType, left: usize, right: usize) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node {
            kind: NodeKind::Binary { op, left, right },
            eval_interval: None,
        });
        id
    }

    /// Menambahkan node Unary Operation (sqr, sqrt)
    pub fn add_unary(&mut self, op: OpType, child: usize) -> usize {
        let id = self.nodes.len();
        self.nodes.push(Node {
            kind: NodeKind::Unary { op, child },
            eval_interval: None,
        });
        id
    }

    /// Step 1 HC4: Evaluasi nilai interval dari daun ke akar
    pub fn forward_eval(&mut self, root: usize, box_region: &BoxRegion) -> Option<Interval> {
        let kind = self.nodes[root].kind.clone();

        let res_interval = match kind {
            NodeKind::Constant(val) => Interval::point(val),

            NodeKind::Variable(ref name) => {
                // Ambil interval variabel saat ini dari BoxRegion
                box_region.get(name).copied()
            }

            NodeKind::Binary { op, left, right } => {
                let l_int = self.forward_eval(left, box_region)?;
                let r_int = self.forward_eval(right, box_region)?;

                match op {
                    OpType::Add => Some(l_int + r_int),
                    OpType::Sub => Some(l_int - r_int),
                    OpType::Mul => Some(l_int * r_int),
                    OpType::Div => l_int / r_int,
                    _ => None,
                }
            }

            NodeKind::Unary { op, child } => {
                let c_int = self.forward_eval(child, box_region)?;

                match op {
                    OpType::Sqr => Some(c_int.sqr()),
                    OpType::Sqrt => c_int.sqrt(),
                    OpType::Sin => Some(c_int.sin()),
                    OpType::Cos => Some(c_int.cos()),
                    OpType::Exp => Some(c_int.exp()),
                    _ => None,
                }
            }
        };

        // Simpan hasil interval ke node
        self.nodes[root].eval_interval = res_interval;
        // Return Option<Interval>
        res_interval
    }

    /// Step 2 HC4: Propagasi mundur dari akar ke daun untuk mengecilkan domain variabel
    pub fn backward_eval(
        &mut self,
        node_idx: usize,
        target_interval: Interval,
        box_region: &mut BoxRegion,
    ) -> bool {
        // 1. Potong interval node saat ini dengan target_interval (Narrowing)
        let current_eval = match self.nodes[node_idx].eval_interval {
            Some(inv) => inv,
            None => return false, // Node belum dievaluasi
        };

        let narrowed_interval = match current_eval.intersect(&target_interval) {
            Some(inv) => inv,
            None => return false, // UNSAT / Conflict detected!
        };

        // Update interval sementara di node ini
        self.nodes[node_idx].eval_interval = Some(narrowed_interval);

        // 2. Propagasi ke anak-anaknya berdasarkan jenis Node
        let kind = self.nodes[node_idx].kind.clone();

        match kind {
            NodeKind::Constant(_) => true, // Tidak bisa diperkecil

            NodeKind::Variable(ref name) => {
                // Update domain variabel utama di BoxRegion!
                if let Some(var_interval) = box_region.get_mut(name) {
                    if let Some(new_inv) = var_interval.intersect(&narrowed_interval) {
                        *var_interval = new_inv;
                        true
                    } else {
                        false // Conflict pada variabel
                    }
                } else {
                    false
                }
            }

            NodeKind::Binary { op, left, right } => {
                let l_eval = self.nodes[left].eval_interval.unwrap();
                let r_eval = self.nodes[right].eval_interval.unwrap();

                match op {
                    OpType::Add => {
                        // z = x + y  =>  x = z - y,  y = z - x
                        let new_l_target = narrowed_interval - r_eval;
                        let new_r_target = narrowed_interval - l_eval;
                        let ok_l = self.backward_eval(left, new_l_target, box_region);
                        let ok_r = self.backward_eval(right, new_r_target, box_region);
                        ok_l && ok_r
                    }
                    OpType::Sub => {
                        // z = x - y  =>  x = z + y,  y = x - z
                        let new_l_target = narrowed_interval + r_eval;
                        let new_r_target = l_eval - narrowed_interval;

                        let res_left = self.backward_eval(left, new_l_target, box_region);
                        let res_right = self.backward_eval(right, new_r_target, box_region);

                        res_left && res_right
                    }

                    OpType::Mul => {
                        // z = x * y  =>  x = z / y,  y = z / x
                        let new_l_target = (narrowed_interval / r_eval).unwrap_or(l_eval);
                        let new_r_target = (narrowed_interval / l_eval).unwrap_or(r_eval);
                        let ok_l = self.backward_eval(left, new_l_target, box_region);
                        let ok_r = self.backward_eval(right, new_r_target, box_region);
                        ok_l && ok_r
                    }

                    _ => true, // Operasi lain bisa ditambahkan nanti
                }
            }

            NodeKind::Unary { op, child } => {
                let c_eval = self.nodes[child].eval_interval.unwrap();

                match op {
                    OpType::Sqr => {
                        // z = x^2  =>  x = sqrt(z) U -sqrt(z)
                        // Untuk interval, jika x bisa negatif dan positif: x = [-sqrt(z.high), sqrt(z.high)]
                        if let Some(sqrt_z) = narrowed_interval.sqrt() {
                            let new_c_target = if c_eval.contains_zero() {
                                Interval::new(-sqrt_z.high, sqrt_z.high).unwrap()
                            } else if c_eval.high <= 0.0 {
                                Interval::new(-sqrt_z.high, -sqrt_z.low).unwrap()
                            } else {
                                sqrt_z
                            };

                            self.backward_eval(child, new_c_target, box_region)
                        } else {
                            false // Sqrt domain error -> Conflict!
                        }
                    }
                    OpType::Exp => {
                        // z = exp(x) => x = ln(z)
                        // Domain z HARUS > 0
                        if narrowed_interval.high <= 0.0 {
                            false // Conflict! exp(x) tidak mungkin <= 0
                        } else {
                            let valid_z = Interval::new(
                                narrowed_interval.low.max(1e-300),
                                narrowed_interval.high,
                            )
                            .unwrap();
                            let ln_z = Interval {
                                low: Interval::round_down(valid_z.low.ln()),
                                high: Interval::round_up(valid_z.high.ln()),
                            };
                            self.backward_eval(child, ln_z, box_region)
                        }
                    }

                    OpType::Sin => {
                        // z = sin(x) => untuk domain lokal [-PI/2, PI/2], x = asin(z)
                        // Nilai z HARUS berada di rentang [-1, 1]
                        if let Some(valid_z) =
                            narrowed_interval.intersect(&Interval::new(-1.0, 1.0).unwrap())
                        {
                            let asin_z = Interval {
                                low: Interval::round_down(valid_z.low.asin()),
                                high: Interval::round_up(valid_z.high.asin()),
                            };

                            // Jika domain asal anak berada di kisaran [-PI/2, PI/2]
                            if c_eval.low >= -std::f64::consts::FRAC_PI_2
                                && c_eval.high <= std::f64::consts::FRAC_PI_2
                            {
                                self.backward_eval(child, asin_z, box_region)
                            } else {
                                // Untuk PoC sederhana pada domain umum: abaikan narrowing jika melintasi beberapa periode
                                true
                            }
                        } else {
                            false // Conflict! sin(x) di luar [-1, 1]
                        }
                    }

                    OpType::Cos => {
                        // z = cos(x) => untuk domain lokal [0, PI], x = acos(z)
                        // Nilai z HARUS berada di rentang [-1, 1]
                        if let Some(valid_z) =
                            narrowed_interval.intersect(&Interval::new(-1.0, 1.0).unwrap())
                        {
                            // acos bersifat monotonically decreasing: high z -> low x
                            let acos_z = Interval {
                                low: Interval::round_down(valid_z.high.acos()),
                                high: Interval::round_up(valid_z.low.acos()),
                            };

                            // Jika domain asal anak berada di kisaran [0, PI]
                            if c_eval.low >= 0.0 && c_eval.high <= std::f64::consts::PI {
                                self.backward_eval(child, acos_z, box_region)
                            } else {
                                true
                            }
                        } else {
                            false // Conflict! cos(x) di luar [-1, 1]
                        }
                    }

                    _ => true,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ast_forward_eval_simple_equation() {
        // Misal membuat ekspresi: x^2 + y
        // x ∈ [2, 3], y ∈ [1, 5]
        let mut ast = Ast::new();

        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let root = ast.add_binary(OpType::Add, x_sqr, y);

        let mut box_region = BoxRegion::default();
        box_region.insert("x".to_string(), Interval::new(2.0, 3.0).unwrap());
        box_region.insert("y".to_string(), Interval::new(1.0, 5.0).unwrap());

        // Evaluasi x^2 + y
        let res = ast.forward_eval(root, &box_region).unwrap();

        // x^2 = [4, 9], y = [1, 5] -> x^2 + y = [5, 14] (dengan rounding)
        assert!(res.low <= 5.0);
        assert!(res.high >= 14.0);
    }

    #[test]
    fn test_hc4_contraction_squeeze() {
        // Constraint: x^2 + y = 5
        // Domain awal: x ∈ [1, 3], y ∈ [0, 2]
        let mut ast = Ast::new();
        let x = ast.add_variable("x");
        let y = ast.add_variable("y");
        let x_sqr = ast.add_unary(OpType::Sqr, x);
        let root = ast.add_binary(OpType::Add, x_sqr, y);

        let mut box_region = BoxRegion::default();
        box_region.insert("x".to_string(), Interval::new(1.0, 3.0).unwrap());
        box_region.insert("y".to_string(), Interval::new(0.0, 2.0).unwrap());

        // 1. Forward Pass
        let _ = ast.forward_eval(root, &box_region).unwrap();

        // 2. Backward Pass: Paksa hasil x^2 + y HARUS bernilai persis [5, 5]
        let target = Interval::point(5.0).unwrap();
        let is_sat = ast.backward_eval(root, target, &mut box_region);

        assert!(is_sat, "Harusnya SAT karena ada solusi");

        let new_x = box_region.get("x").unwrap();
        let new_y = box_region.get("y").unwrap();

        // Analisa Matematika:
        // x^2 = 5 - y => Karena y ∈ [0, 2], maka x^2 ∈ [3, 5]
        // Seharusnya x yang tadinya [1, 3] menguncup/terpotong menjadi [sqrt(3), sqrt(5)] ≈ [1.73, 2.23]
        assert!(
            new_x.low > 1.5,
            "Bound bawah x harus naik mendekati sqrt(3)"
        );
        assert!(
            new_x.high < 2.5,
            "Bound atas x harus turun mendekati sqrt(5)"
        );

        println!("Contracted x: {:?}", new_x);
        println!("Contracted y: {:?}", new_y);
    }
}
