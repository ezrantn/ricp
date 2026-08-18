use std::ops::{ Add, Div, Mul, Sub };

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Interval {
    pub low: f64,
    pub high: f64,
}

impl Interval {
    /// Membuat interval baru [low, high].
    /// Mengembalikan None jika low > high atau ada nilainya yang NaN.
    pub fn new(low: f64, high: f64) -> Option<Self> {
        if low.is_nan() || high.is_nan() || low > high { None } else { Some(Self { low, high }) }
    }

    /// Point interval [v, v]
    pub fn point(v: f64) -> Option<Self> {
        Self::new(v, v)
    }

    /// Lebar dari interval (width)
    #[inline]
    pub fn width(&self) -> f64 {
        self.high - self.low
    }

    /// Titik tengah interval (midpoint)
    #[inline]
    pub fn mid(&self) -> f64 {
        0.5 * (self.low + self.high)
    }

    /// Cek apakah interval berisi titik 0
    #[inline]
    pub fn contains_zero(&self) -> bool {
        self.low <= 0.0 && self.high >= 0.0
    }

    /// Interseksi dua interval [A] ∩ [B]
    /// Krusial untuk proses Contraction/Pruning!
    #[inline]
    pub fn intersect(&self, other: &Self) -> Option<Self> {
        let new_low = self.low.max(other.low);
        let new_high = self.high.min(other.high);
        Self::new(new_low, new_high)
    }

    /// Batas aman ULP untuk fungsi TRANSCENDENTAL (exp, sin, cos, ln, asin, acos).
    /// IEEE-754 TIDAK mewajibkan fungsi-fungsi ini correctly-rounded (beda dengan
    /// +, -, *, /, sqrt yang wajib <=0.5 ulp). libm (glibc/musl/MSVC CRT) pada
    /// praktiknya biasanya akurat <=1 ulp, tapi itu bukan garansi lintas-platform.
    /// Margin 4 ulp ini adalah bound rekayasa (bukan bukti formal) untuk
    /// mengkompensasi variasi implementasi libm tsb, dijaga tetap murah karena
    /// murni operasi bit native f64 (tanpa dependency arbitrary-precision).
    const TRANSCENDENTAL_ULP_MARGIN: u32 = 4;

    /// Mengarahkan rounding ke bawah (-infinity)
    #[inline]
    pub fn round_down(val: f64) -> f64 {
        val.next_down()
    }

    /// Mengarahkan rounding ke atas (+infinity)
    #[inline]
    pub fn round_up(val: f64) -> f64 {
        val.next_up()
    }

    /// Rounding ke bawah + safety margin ULP, khusus hasil fungsi transcendental.
    #[inline]
    pub fn round_down_transcendental(val: f64) -> f64 {
        let mut v = val;
        for _ in 0..Self::TRANSCENDENTAL_ULP_MARGIN {
            v = v.next_down();
        }

        v
    }

    /// Rounding ke atas + safety margin ULP, khusus hasil fungsi transcendental.
    #[inline]
    pub fn round_up_transcendental(val: f64) -> f64 {
        let mut v = val;
        for _ in 0..Self::TRANSCENDENTAL_ULP_MARGIN {
            v = v.next_up();
        }

        v
    }

    /// Operasi Kuadrat: [x]^2
    #[inline]
    pub fn sqr(&self) -> Self {
        if self.contains_zero() {
            let h2_a = self.low * self.low;
            let h2_b = self.high * self.high;
            Self {
                low: 0.0,
                high: Self::round_up(h2_a.max(h2_b)),
            }
        } else {
            let l2 = self.low * self.low;
            let h2 = self.high * self.high;
            Self {
                low: Self::round_down(l2.min(h2)),
                high: Self::round_up(l2.max(h2)),
            }
        }
    }

    /// Akar Kuadrat: sqrt([x])
    pub fn sqrt(&self) -> Option<Self> {
        if self.high < 0.0 {
            None // Tidak ada domain riil
        } else {
            let low = if self.low <= 0.0 { 0.0 } else { Self::round_down(self.low.sqrt()) };
            let high = Self::round_up(self.high.sqrt());
            Self::new(low, high)
        }
    }

    /// Eksponensial: exp([x])
    pub fn exp(&self) -> Self {
        Self {
            low: Self::round_down_transcendental(self.low.exp()),
            high: Self::round_up_transcendental(self.high.exp()),
        }
    }

    /// Sinus: sin([x])
    pub fn sin(&self) -> Self {
        use std::f64::consts::TAU; // 2 * PI

        // Jika lebar interval >= 2*PI, maka sin([x]) pasti mencakup seluruh rentang [-1, 1]
        if self.width() >= TAU {
            return Self::new(-1.0, 1.0).unwrap();
        }

        let l_sin = self.low.sin();
        let h_sin = self.high.sin();

        let mut low = l_sin.min(h_sin);
        let mut high = l_sin.max(h_sin);

        // Cek apakah interval melintasi puncak sin (PI/2 + 2k*PI -> sin = 1.0)
        let k_high = ((self.high - std::f64::consts::FRAC_PI_2) / TAU).floor();
        let peak = std::f64::consts::FRAC_PI_2 + k_high * TAU;
        if self.low <= peak && peak <= self.high {
            high = 1.0;
        }

        // Cek apakah interval melintasi lembah sin (3*PI/2 + 2k*PI -> sin = -1.0)
        let k_low = ((self.high - 3.0 * std::f64::consts::FRAC_PI_2) / TAU).floor();
        let trough = 3.0 * std::f64::consts::FRAC_PI_2 + k_low * TAU;
        if self.low <= trough && trough <= self.high {
            low = -1.0;
        }

        Self {
            low: Self::round_down_transcendental(low),
            high: Self::round_up_transcendental(high),
        }
    }

    /// Cosinus: cos([x])
    #[inline]
    pub fn cos(&self) -> Self {
        use std::f64::consts::TAU;

        if self.width() >= TAU {
            return Self::new(-1.0, 1.0).unwrap();
        }

        let l_cos = self.low.cos();
        let h_cos = self.high.cos();

        let mut low = l_cos.min(h_cos);
        let mut high = l_cos.max(h_cos);

        // Cek puncak cos (2k*PI -> cos = 1.0)
        let k_high = (self.high / TAU).floor();
        let peak = k_high * TAU;
        if self.low <= peak && peak <= self.high {
            high = 1.0;
        }

        // Cek lembah cos (PI + 2k*PI -> cos = -1.0)
        let k_low = ((self.high - std::f64::consts::PI) / TAU).floor();
        let trough = std::f64::consts::PI + k_low * TAU;
        if self.low <= trough && trough <= self.high {
            low = -1.0;
        }

        Self {
            low: Self::round_down_transcendental(low),
            high: Self::round_up_transcendental(high),
        }
    }
}

impl Add for Interval {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            low: Interval::round_down(self.low + rhs.low),
            high: Interval::round_up(self.high + rhs.high),
        }
    }
}

impl Sub for Interval {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            low: Interval::round_down(self.low - rhs.high),
            high: Interval::round_up(self.high - rhs.low),
        }
    }
}

impl Mul for Interval {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        if self.low >= 0.0 {
            if rhs.low >= 0.0 {
                // Case 1: [+ +] * [+ +]
                Self {
                    low: Self::round_down(self.low * rhs.low),
                    high: Self::round_up(self.high * rhs.high),
                }
            } else if rhs.high <= 0.0 {
                // Case 2: [+ +] * [- -]
                Self {
                    low: Self::round_down(self.high * rhs.low),
                    high: Self::round_up(self.low * rhs.high),
                }
            } else {
                // Case 3: [+ +] * [- +]
                Self {
                    low: Self::round_down(self.high * rhs.low),
                    high: Self::round_up(self.high * rhs.high),
                }
            }
        } else if self.high <= 0.0 {
            if rhs.low >= 0.0 {
                // Case 4: [- -] * [+ +]
                Self {
                    low: Self::round_down(self.low * rhs.high),
                    high: Self::round_up(self.high * rhs.low),
                }
            } else if rhs.high <= 0.0 {
                // Case 5: [- -] * [- -]
                Self {
                    low: Self::round_down(self.high * rhs.high),
                    high: Self::round_up(self.low * rhs.low),
                }
            } else {
                // Case 6: [- -] * [- +]
                Self {
                    low: Self::round_down(self.low * rhs.high),
                    high: Self::round_up(self.low * rhs.low),
                }
            }
        } else {
            if rhs.low >= 0.0 {
                // Case 7: [- +] * [+ +]
                Self {
                    low: Self::round_down(self.low * rhs.high),
                    high: Self::round_up(self.high * rhs.high),
                }
            } else if rhs.high <= 0.0 {
                // Case 8: [- +] * [- -]
                Self {
                    low: Self::round_down(self.high * rhs.low),
                    high: Self::round_up(self.low * rhs.low),
                }
            } else {
                // Case 9: [- +] * [- +] (Kedua interval melintasi angka 0)
                // Hanya di kasus ini kita butuh 4 perkalian & min/max
                let p1 = self.low * rhs.low;
                let p2 = self.low * rhs.high;
                let p3 = self.high * rhs.low;
                let p4 = self.high * rhs.high;

                Self {
                    low: Self::round_down(p2.min(p3)),
                    high: Self::round_up(p1.max(p4)),
                }
            }
        }
    }
}

impl Div for Interval {
    type Output = Option<Self>;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        if rhs.contains_zero() {
            // Pembagian dengan interval yang memuat 0 menghasilkan interval tak hingga.
            // Untuk PoC, kita return None jika divisor mencakup 0 (atau tangani khusus nanti).
            None
        } else {
            let inv = Interval {
                low: Interval::round_down(1.0 / rhs.high),
                high: Interval::round_up(1.0 / rhs.low),
            };
            Some(self * inv)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sound_addition() {
        let a = Interval::new(1.0, 2.0).unwrap();
        let b = Interval::new(3.0, 4.0).unwrap();
        let c = a + b;

        assert!(c.low <= 4.0);
        assert!(c.high >= 6.0);
    }

    // exp/sin/cos are NOT IEEE-754 required-correctly-rounded (unlike sqrt),
    // so their outward rounding needs a wider safety margin than a single ULP
    // to stay sound across libm implementations.
    #[test]
    fn test_transcendental_margin_wider_than_single_ulp() {
        let raw = 1.0_f64;

        let single_ulp_down = Interval::round_down(raw);
        let single_ulp_up = Interval::round_up(raw);

        let margin_down = Interval::round_down_transcendental(raw);
        let margin_up = Interval::round_up_transcendental(raw);

        // Margin harus mengucup lebih lebar (atau sama) dibanding 1-ulp biasa,
        // supaya bisa menyerap potensi error libm > 0.5 ulp pada exp/sin/cos.
        assert!(margin_down < single_ulp_down);
        assert!(margin_up > single_ulp_up);

        // Tapi tetap membungkus nilai mentahnya (soundness dasar tetap terjaga)
        assert!(margin_down <= raw);
        assert!(margin_up >= raw);
    }

    #[test]
    fn test_exp_result_uses_transcendental_margin() {
        // exp([1, 1]) harus punya lebar > 0 (margin membuat titik jadi interval sempit,
        // bukan titik tunggal seperti pembulatan 1-ulp biasa akan hasilkan)
        let a = Interval::point(1.0).unwrap();
        let res = a.exp();

        assert!(res.low <= std::f64::consts::E);
        assert!(res.high >= std::f64::consts::E);
        // Lebar interval harus lebih besar dari sekadar 2 ulp (1 ulp di tiap sisi),
        // membuktikan margin transcendental benar-benar dipakai.
        assert!(res.width() > 2.0 * f64::EPSILON * std::f64::consts::E);
    }

    #[test]
    fn test_intersection() {
        let a = Interval::new(1.0, 5.0).unwrap();
        let b = Interval::new(3.0, 7.0).unwrap();
        let c = a.intersect(&b).unwrap();

        assert_eq!(c, Interval::new(3.0, 5.0).unwrap());
    }

    #[test]
    fn test_unsat_intersection() {
        let a = Interval::new(1.0, 2.0).unwrap();
        let b = Interval::new(3.0, 4.0).unwrap();

        // Interseksi interval terpisah harus menghasilkan None (Conflict/UNSAT)
        assert_eq!(a.intersect(&b), None);
    }

    #[test]
    fn test_sqr_contains_zero() {
        let a = Interval::new(-2.0, 3.0).unwrap();
        let sq = a.sqr();

        // [-2, 3]^2 harus menghasilkan [0, 9] (dengan rounding up pada 9)
        assert_eq!(sq.low, 0.0);
        assert!(sq.high >= 9.0);
    }

    #[test]
    fn test_soundness_addition_rounding() {
        // 0.1 dan 0.2 tidak tepat di f64.
        let a = Interval::new(0.1, 0.2).unwrap();
        let b = Interval::new(0.2, 0.4).unwrap();
        let c = a + b;

        // 1. Uji bahwasanya interval c membungkus nilai penjumlahan mentah f64 (a.low + b.low)
        let raw_sum_low = a.low + b.low;
        let raw_sum_high = a.high + b.high;

        // Direct rounding HARUS memperlebar batas dari kalkulasi mentah f64
        assert!(c.low < raw_sum_low, "low bound harus ditarik ke bawah oleh next_down()");
        assert!(c.high > raw_sum_high, "high bound harus ditarik ke atas oleh next_up()");

        // 2. c.low dijamin <= 0.3 f64 literal
        assert!(c.low <= 0.3);
        assert!(c.high >= 0.6);
    }

    #[test]
    fn test_subtraction_bound_swapping() {
        // [a, b] - [c, d] = [a - d, b - c]
        let a = Interval::new(10.0, 20.0).unwrap();
        let b = Interval::new(3.0, 5.0).unwrap();
        let res = a - b;

        // low bound = 10 - 5 = 5 (rounded down)
        // high bound = 20 - 3 = 17 (rounded up)
        assert!(res.low <= 5.0);
        assert!(res.high >= 17.0);
    }

    #[test]
    fn test_multiplication_all_sign_quadrants() {
        // ICP sering memproses interval dengan kombinasi tanda (+/-) yang bervariasi.

        // Positif x Positif
        let p1 = Interval::new(2.0, 3.0).unwrap() * Interval::new(4.0, 5.0).unwrap();
        assert!(p1.low <= 8.0 && p1.high >= 15.0);

        // Negatif x Positif
        let p2 = Interval::new(-3.0, -2.0).unwrap() * Interval::new(2.0, 4.0).unwrap();
        assert!(p2.low <= -12.0 && p2.high >= -4.0);

        // Melintasi Nol x Positif
        let p3 = Interval::new(-2.0, 3.0).unwrap() * Interval::new(2.0, 4.0).unwrap();
        assert!(p3.low <= -8.0 && p3.high >= 12.0);

        // Negatif x Negatif
        let p4 = Interval::new(-4.0, -2.0).unwrap() * Interval::new(-5.0, -3.0).unwrap();
        assert!(p4.low <= 6.0 && p4.high >= 20.0);
    }

    // ==========================================
    // 2. DIVISION & ZERO-CROSSING (ICP CONTRACTOR CRITICAL)
    // ==========================================

    #[test]
    fn test_division_valid() {
        let a = Interval::new(10.0, 20.0).unwrap();
        let b = Interval::new(2.0, 5.0).unwrap();
        let res = (a / b).unwrap();

        // 10/5 = 2.0, 20/2 = 10.0
        assert!(res.low <= 2.0);
        assert!(res.high >= 10.0);
    }

    #[test]
    fn test_division_by_zero_contains_zero_returns_none() {
        let a = Interval::new(1.0, 5.0).unwrap();
        let zero_interval = Interval::new(-1.0, 1.0).unwrap();

        // Di ICP sederhana, membagi dengan interval yang memuat 0 harus ditolak/dihanling khusus
        assert_eq!(a / zero_interval, None);
    }

    // ==========================================
    // 3. NON-LINEAR OPERATIONS (SQR & SQRT)
    // ==========================================

    #[test]
    fn test_sqr_spanning_zero() {
        // Scenario: [-3, 2]^2 -> Nilai terkecil pasti 0, nilai terbesar max((-3)^2, 2^2) = 9
        let a = Interval::new(-3.0, 2.0).unwrap();
        let res = a.sqr();

        assert_eq!(res.low, 0.0);
        assert!(res.high >= 9.0);
    }

    #[test]
    fn test_sqr_strictly_negative() {
        // Scenario: [-5, -2]^2 -> Nilai berada di [4, 25]
        let a = Interval::new(-5.0, -2.0).unwrap();
        let res = a.sqr();

        assert!(res.low <= 4.0);
        assert!(res.high >= 25.0);
    }

    #[test]
    fn test_sqrt_domain_pruning() {
        // Domain x >= 0
        let valid = Interval::new(4.0, 16.0).unwrap();
        let res = valid.sqrt().unwrap();
        assert!(res.low <= 2.0);
        assert!(res.high >= 4.0);

        // Domain melintasi nol [-4, 9] -> Terpotong otomatis jadi [0, 3]
        let partial_valid = Interval::new(-4.0, 9.0).unwrap();
        let res_partial = partial_valid.sqrt().unwrap();
        assert_eq!(res_partial.low, 0.0);
        assert!(res_partial.high >= 3.0);

        // Domain murni negatif -> Harus UNSAT (None)
        let invalid = Interval::new(-10.0, -2.0).unwrap();
        assert_eq!(invalid.sqrt(), None);
    }

    // ==========================================
    // 4. CONFLICT & CONTRACTION SCENARIOS (HC4 PRUNING)
    // ==========================================

    #[test]
    fn test_box_intersection_success() {
        // Simulasi contractor memperkecil box variabel x dari [0, 10] menjadi [3, 5]
        let x_current = Interval::new(0.0, 10.0).unwrap();
        let x_contracted = Interval::new(3.0, 5.0).unwrap();

        let new_x = x_current.intersect(&x_contracted).unwrap();
        assert_eq!(new_x, Interval::new(3.0, 5.0).unwrap());
    }

    #[test]
    fn test_box_intersection_conflict_unsat() {
        // Simulasi ditemukannya konflik pada cabang (Box ini terbukti UNSAT)
        // Misal x HARUS di [0, 2] tapi constraint lain minta x di [5, 10]
        let x_domain = Interval::new(0.0, 2.0).unwrap();
        let constraint_domain = Interval::new(5.0, 10.0).unwrap();

        assert_eq!(x_domain.intersect(&constraint_domain), None);
    }

    #[test]
    fn test_point_interval_intersection() {
        // Kasus ketika interval menguncup jadi 1 titik (konstanta)
        let a = Interval::point(5.0).unwrap();
        let b = Interval::new(0.0, 10.0).unwrap();

        let res = a.intersect(&b).unwrap();
        assert!(res.low <= 5.0 && res.high >= 5.0);
    }
}
