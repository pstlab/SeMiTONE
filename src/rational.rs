use rug::Complete;
use std::{fmt, ops};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rational {
    NegativeInf,
    Finite(rug::Rational),
    PositiveInf,
}

impl Rational {
    pub fn zero() -> Self {
        Self::Finite(rug::Rational::from(0))
    }

    pub fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }

    pub fn is_positive(&self) -> bool {
        matches!(self, Self::Finite(r) if r.is_positive()) || matches!(self, Self::PositiveInf)
    }

    pub fn is_negative(&self) -> bool {
        matches!(self, Self::Finite(r) if r.is_negative()) || matches!(self, Self::NegativeInf)
    }

    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Finite(r) if r.is_integer())
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Self::Finite(r) if r.is_zero())
    }

    fn finite_sign(r: &rug::Rational) -> i8 {
        if r.is_positive() {
            1
        } else if r.is_negative() {
            -1
        } else {
            0
        }
    }

    fn add_ref(lhs: &Self, rhs: &Self) -> Self {
        use Rational::*;

        match (lhs, rhs) {
            (NegativeInf, PositiveInf) | (PositiveInf, NegativeInf) => {
                panic!("undefined operation: -inf + +inf")
            }
            (NegativeInf, _) | (_, NegativeInf) => NegativeInf,
            (PositiveInf, _) | (_, PositiveInf) => PositiveInf,
            (Finite(a), Finite(b)) => Finite((a + b).complete()),
        }
    }

    fn mul_ref(lhs: &Self, rhs: &Self) -> Self {
        use Rational::*;

        match (lhs, rhs) {
            (Finite(a), Finite(b)) => Finite((a * b).complete()),

            (NegativeInf, Finite(r)) | (Finite(r), NegativeInf) => match Self::finite_sign(r) {
                1 => NegativeInf,
                -1 => PositiveInf,
                _ => panic!("undefined operation: -inf * 0"),
            },

            (PositiveInf, Finite(r)) | (Finite(r), PositiveInf) => match Self::finite_sign(r) {
                1 => PositiveInf,
                -1 => NegativeInf,
                _ => panic!("undefined operation: +inf * 0"),
            },

            (NegativeInf, NegativeInf) | (PositiveInf, PositiveInf) => PositiveInf,
            (NegativeInf, PositiveInf) | (PositiveInf, NegativeInf) => NegativeInf,
        }
    }

    fn div_ref(lhs: &Self, rhs: &Self) -> Self {
        use Rational::*;

        match (lhs, rhs) {
            (Finite(a), Finite(b)) => {
                if b.is_zero() {
                    match Self::finite_sign(a) {
                        1 => PositiveInf,
                        -1 => NegativeInf,
                        _ => panic!("undefined operation: 0 / 0"),
                    }
                } else {
                    Finite((a / b).complete())
                }
            }

            (NegativeInf, Finite(r)) => match Self::finite_sign(r) {
                1 => NegativeInf,
                -1 => PositiveInf,
                _ => panic!("undefined operation: -inf / 0"),
            },

            (PositiveInf, Finite(r)) => match Self::finite_sign(r) {
                1 => PositiveInf,
                -1 => NegativeInf,
                _ => panic!("undefined operation: +inf / 0"),
            },

            (Finite(_), NegativeInf) | (Finite(_), PositiveInf) => Rational::zero(),

            (NegativeInf, NegativeInf) | (NegativeInf, PositiveInf) | (PositiveInf, NegativeInf) | (PositiveInf, PositiveInf) => {
                panic!("undefined operation: ±inf / ±inf")
            }
        }
    }
}

impl Default for Rational {
    fn default() -> Self {
        Self::zero()
    }
}

impl ops::Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        use Rational::*;

        match self {
            NegativeInf => PositiveInf,
            Finite(r) => Finite(-r),
            PositiveInf => NegativeInf,
        }
    }
}

impl ops::Neg for &Rational {
    type Output = Rational;

    fn neg(self) -> Self::Output {
        use Rational::*;

        match self {
            NegativeInf => PositiveInf,
            Finite(r) => Finite(-r.clone()),
            PositiveInf => NegativeInf,
        }
    }
}

impl ops::Add for Rational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Rational::add_ref(&self, &rhs)
    }
}

impl ops::Add<&Rational> for Rational {
    type Output = Self;

    fn add(self, rhs: &Rational) -> Self::Output {
        Rational::add_ref(&self, rhs)
    }
}

impl ops::Add<Rational> for &Rational {
    type Output = Rational;

    fn add(self, rhs: Rational) -> Self::Output {
        Rational::add_ref(self, &rhs)
    }
}

impl ops::Add<&Rational> for &Rational {
    type Output = Rational;

    fn add(self, rhs: &Rational) -> Self::Output {
        Rational::add_ref(self, rhs)
    }
}

impl ops::AddAssign for Rational {
    fn add_assign(&mut self, rhs: Self) {
        *self = Rational::add_ref(self, &rhs);
    }
}

impl ops::AddAssign<&Rational> for Rational {
    fn add_assign(&mut self, rhs: &Rational) {
        *self = Rational::add_ref(self, rhs);
    }
}

impl ops::Sub for Rational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl ops::Sub<&Rational> for Rational {
    type Output = Self;

    fn sub(self, rhs: &Rational) -> Self::Output {
        self + (-rhs)
    }
}

impl ops::Sub<Rational> for &Rational {
    type Output = Rational;

    fn sub(self, rhs: Rational) -> Self::Output {
        self + (-rhs)
    }
}

impl ops::Sub<&Rational> for &Rational {
    type Output = Rational;

    fn sub(self, rhs: &Rational) -> Self::Output {
        self + (-rhs)
    }
}

impl ops::SubAssign for Rational {
    fn sub_assign(&mut self, rhs: Self) {
        *self = Rational::add_ref(self, &(-rhs));
    }
}

impl ops::SubAssign<&Rational> for Rational {
    fn sub_assign(&mut self, rhs: &Rational) {
        *self = Rational::add_ref(self, &(-rhs));
    }
}

impl ops::Mul for Rational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Rational::mul_ref(&self, &rhs)
    }
}

impl ops::Mul<&Rational> for Rational {
    type Output = Self;

    fn mul(self, rhs: &Rational) -> Self::Output {
        Rational::mul_ref(&self, rhs)
    }
}

impl ops::Mul<Rational> for &Rational {
    type Output = Rational;

    fn mul(self, rhs: Rational) -> Self::Output {
        Rational::mul_ref(self, &rhs)
    }
}

impl ops::Mul<&Rational> for &Rational {
    type Output = Rational;

    fn mul(self, rhs: &Rational) -> Self::Output {
        Rational::mul_ref(self, rhs)
    }
}

impl ops::MulAssign for Rational {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Rational::mul_ref(self, &rhs);
    }
}

impl ops::MulAssign<&Rational> for Rational {
    fn mul_assign(&mut self, rhs: &Rational) {
        *self = Rational::mul_ref(self, rhs);
    }
}

impl ops::Div for Rational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Rational::div_ref(&self, &rhs)
    }
}

impl ops::Div<&Rational> for Rational {
    type Output = Self;

    fn div(self, rhs: &Rational) -> Self::Output {
        Rational::div_ref(&self, rhs)
    }
}

impl ops::Div<Rational> for &Rational {
    type Output = Rational;

    fn div(self, rhs: Rational) -> Self::Output {
        Rational::div_ref(self, &rhs)
    }
}

impl ops::Div<&Rational> for &Rational {
    type Output = Rational;

    fn div(self, rhs: &Rational) -> Self::Output {
        Rational::div_ref(self, rhs)
    }
}

impl ops::DivAssign for Rational {
    fn div_assign(&mut self, rhs: Self) {
        *self = Rational::div_ref(self, &rhs);
    }
}

impl ops::DivAssign<&Rational> for Rational {
    fn div_assign(&mut self, rhs: &Rational) {
        *self = Rational::div_ref(self, rhs);
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rational::NegativeInf => write!(f, "-inf"),
            Rational::Finite(r) => write!(f, "{r}"),
            Rational::PositiveInf => write!(f, "+inf"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InfRational {
    rat: Rational,
    inf: rug::Rational,
}

impl InfRational {
    pub fn new(rat: Rational, inf: rug::Rational) -> Self {
        let inf = if rat.is_finite() { inf } else { rug::Rational::from(0) };

        Self { rat, inf }
    }

    pub fn rational_part(&self) -> &Rational {
        &self.rat
    }

    pub fn infinitesimal_part(&self) -> &rug::Rational {
        &self.inf
    }

    pub fn into_parts(self) -> (Rational, rug::Rational) {
        (self.rat, self.inf)
    }
}

impl Default for InfRational {
    fn default() -> Self {
        Self::new(Rational::zero(), rug::Rational::from(0))
    }
}

impl ops::Neg for InfRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.rat, -self.inf)
    }
}

impl ops::Neg for &InfRational {
    type Output = InfRational;

    fn neg(self) -> Self::Output {
        InfRational::new(-&self.rat, -self.inf.clone())
    }
}

impl ops::Add for InfRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.rat + rhs.rat, self.inf + rhs.inf)
    }
}

impl ops::Add<&InfRational> for InfRational {
    type Output = Self;

    fn add(self, rhs: &InfRational) -> Self::Output {
        Self::new(self.rat + &rhs.rat, self.inf + &rhs.inf)
    }
}

impl ops::Add<InfRational> for &InfRational {
    type Output = InfRational;

    fn add(self, rhs: InfRational) -> Self::Output {
        InfRational::new(&self.rat + rhs.rat, &self.inf + rhs.inf)
    }
}

impl ops::Add<&InfRational> for &InfRational {
    type Output = InfRational;

    fn add(self, rhs: &InfRational) -> Self::Output {
        InfRational::new(&self.rat + &rhs.rat, (&self.inf + &rhs.inf).complete())
    }
}

impl ops::AddAssign for InfRational {
    fn add_assign(&mut self, rhs: Self) {
        self.rat += rhs.rat;
        self.inf += rhs.inf;

        if !self.rat.is_finite() {
            self.inf = rug::Rational::from(0);
        }
    }
}

impl ops::AddAssign<&InfRational> for InfRational {
    fn add_assign(&mut self, rhs: &InfRational) {
        self.rat += &rhs.rat;
        self.inf += &rhs.inf;

        if !self.rat.is_finite() {
            self.inf = rug::Rational::from(0);
        }
    }
}

impl ops::Sub for InfRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.rat - rhs.rat, self.inf - rhs.inf)
    }
}

impl ops::Sub<&InfRational> for InfRational {
    type Output = Self;

    fn sub(self, rhs: &InfRational) -> Self::Output {
        Self::new(self.rat - &rhs.rat, self.inf - &rhs.inf)
    }
}

impl ops::Sub<InfRational> for &InfRational {
    type Output = InfRational;

    fn sub(self, rhs: InfRational) -> Self::Output {
        InfRational::new(&self.rat - rhs.rat, &self.inf - rhs.inf)
    }
}

impl ops::Sub<&InfRational> for &InfRational {
    type Output = InfRational;

    fn sub(self, rhs: &InfRational) -> Self::Output {
        InfRational::new(&self.rat - &rhs.rat, (&self.inf - &rhs.inf).complete())
    }
}

impl ops::SubAssign for InfRational {
    fn sub_assign(&mut self, rhs: Self) {
        self.rat -= rhs.rat;
        self.inf -= rhs.inf;

        if !self.rat.is_finite() {
            self.inf = rug::Rational::from(0);
        }
    }
}

impl ops::SubAssign<&InfRational> for InfRational {
    fn sub_assign(&mut self, rhs: &InfRational) {
        self.rat -= &rhs.rat;
        self.inf -= &rhs.inf;

        if !self.rat.is_finite() {
            self.inf = rug::Rational::from(0);
        }
    }
}

impl ops::Mul<rug::Rational> for InfRational {
    type Output = Self;

    fn mul(self, rhs: rug::Rational) -> Self::Output {
        self * &rhs
    }
}

impl ops::Mul<&rug::Rational> for InfRational {
    type Output = Self;

    fn mul(mut self, rhs: &rug::Rational) -> Self::Output {
        self.rat *= Rational::Finite(rhs.clone());
        self.inf *= rhs;

        Self::new(self.rat, self.inf)
    }
}

impl ops::Mul<&rug::Rational> for &InfRational {
    type Output = InfRational;

    fn mul(self, rhs: &rug::Rational) -> Self::Output {
        InfRational::new(&self.rat * Rational::Finite(rhs.clone()), (&self.inf * rhs).complete())
    }
}

impl ops::MulAssign<rug::Rational> for InfRational {
    fn mul_assign(&mut self, rhs: rug::Rational) {
        *self *= &rhs;
    }
}

impl ops::MulAssign<&rug::Rational> for InfRational {
    fn mul_assign(&mut self, rhs: &rug::Rational) {
        self.rat *= Rational::Finite(rhs.clone());
        self.inf *= rhs;

        if !self.rat.is_finite() {
            self.inf = rug::Rational::from(0);
        }
    }
}

impl ops::Div<rug::Rational> for InfRational {
    type Output = Self;

    fn div(self, rhs: rug::Rational) -> Self::Output {
        self / &rhs
    }
}

impl ops::Div<&rug::Rational> for InfRational {
    type Output = Self;

    fn div(self, rhs: &rug::Rational) -> Self::Output {
        if rhs.is_zero() {
            panic!("undefined operation: InfRational / 0");
        }

        InfRational::new(self.rat / Rational::Finite(rhs.clone()), self.inf / rhs)
    }
}

impl ops::Div<rug::Rational> for &InfRational {
    type Output = InfRational;

    fn div(self, rhs: rug::Rational) -> Self::Output {
        self / &rhs
    }
}

impl ops::Div<&rug::Rational> for &InfRational {
    type Output = InfRational;

    fn div(self, rhs: &rug::Rational) -> Self::Output {
        if rhs.is_zero() {
            panic!("undefined operation: InfRational / 0");
        }

        InfRational::new(&self.rat / Rational::Finite(rhs.clone()), (&self.inf / rhs).complete())
    }
}

impl ops::DivAssign<rug::Rational> for InfRational {
    fn div_assign(&mut self, rhs: rug::Rational) {
        *self /= &rhs;
    }
}

impl ops::DivAssign<&rug::Rational> for InfRational {
    fn div_assign(&mut self, rhs: &rug::Rational) {
        if rhs.is_zero() {
            panic!("undefined operation: InfRational / 0");
        }

        self.rat /= Rational::Finite(rhs.clone());
        self.inf /= rhs;

        if !self.rat.is_finite() {
            self.inf = rug::Rational::from(0);
        }
    }
}

impl fmt::Display for InfRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.inf.is_zero() {
            write!(f, "{}", self.rat)
        } else if self.inf.is_positive() {
            write!(f, "{} + {}ϵ", self.rat, self.inf)
        } else {
            write!(f, "{} - {}ϵ", self.rat, -self.inf.clone())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fin(n: i32, d: i32) -> Rational {
        Rational::Finite(rug::Rational::from((n, d)))
    }

    fn int(n: i32) -> Rational {
        Rational::Finite(rug::Rational::from(n))
    }

    // --- Default ---

    #[test]
    fn default_is_zero() {
        assert_eq!(Rational::default(), int(0));
    }

    // --- Display ---

    #[test]
    fn display_neg_inf() {
        assert_eq!(Rational::NegativeInf.to_string(), "-inf");
    }

    #[test]
    fn display_pos_inf() {
        assert_eq!(Rational::PositiveInf.to_string(), "+inf");
    }

    #[test]
    fn display_finite() {
        assert_eq!(int(3).to_string(), "3");
        assert_eq!(fin(1, 2).to_string(), "1/2");
    }

    // --- Ordering ---

    #[test]
    fn ordering_neg_inf_lt_finite_lt_pos_inf() {
        assert!(Rational::NegativeInf < int(0));
        assert!(int(0) < Rational::PositiveInf);
        assert!(Rational::NegativeInf < Rational::PositiveInf);
    }

    #[test]
    fn ordering_finite_values() {
        assert!(int(-1) < int(0));
        assert!(int(0) < int(1));
        assert!(fin(1, 3) < fin(1, 2));
    }

    #[test]
    fn ordering_equal() {
        assert_eq!(int(2), int(2));
        assert_eq!(fin(2, 4), fin(1, 2));
        assert_eq!(Rational::NegativeInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf, Rational::PositiveInf);
    }

    // --- Neg ---

    #[test]
    fn neg_neg_inf_is_pos_inf() {
        assert_eq!(-Rational::NegativeInf, Rational::PositiveInf);
    }

    #[test]
    fn neg_pos_inf_is_neg_inf() {
        assert_eq!(-Rational::PositiveInf, Rational::NegativeInf);
    }

    #[test]
    fn neg_finite() {
        assert_eq!(-int(3), int(-3));
        assert_eq!(-fin(1, 2), fin(-1, 2));
        assert_eq!(-int(0), int(0));
    }

    // --- Add ---

    #[test]
    fn add_finite_finite() {
        assert_eq!(int(2) + int(3), int(5));
        assert_eq!(fin(1, 2) + fin(1, 2), int(1));
        assert_eq!(int(-1) + int(1), int(0));
    }

    #[test]
    fn add_inf_absorbs() {
        assert_eq!(Rational::NegativeInf + int(999), Rational::NegativeInf);
        assert_eq!(int(999) + Rational::NegativeInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf + int(-999), Rational::PositiveInf);
        assert_eq!(int(-999) + Rational::PositiveInf, Rational::PositiveInf);
    }

    #[test]
    fn add_same_inf() {
        assert_eq!(Rational::NegativeInf + Rational::NegativeInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf + Rational::PositiveInf, Rational::PositiveInf);
    }

    #[test]
    #[should_panic(expected = "-inf + +inf")]
    fn add_neg_inf_pos_inf_panics() {
        let _ = Rational::NegativeInf + Rational::PositiveInf;
    }

    #[test]
    #[should_panic(expected = "-inf + +inf")]
    fn add_pos_inf_neg_inf_panics() {
        let _ = Rational::PositiveInf + Rational::NegativeInf;
    }

    // --- AddAssign ---

    #[test]
    fn add_assign_finite() {
        let mut a = int(1);
        a += int(2);
        assert_eq!(a, int(3));
    }

    #[test]
    fn add_assign_inf() {
        let mut a = int(5);
        a += Rational::PositiveInf;
        assert_eq!(a, Rational::PositiveInf);
    }

    // --- Sub ---

    #[test]
    fn sub_finite() {
        assert_eq!(int(5) - int(3), int(2));
        assert_eq!(int(0) - int(1), int(-1));
    }

    #[test]
    fn sub_inf() {
        assert_eq!(Rational::PositiveInf - int(100), Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf - int(100), Rational::NegativeInf);
        assert_eq!(int(0) - Rational::PositiveInf, Rational::NegativeInf);
        assert_eq!(int(0) - Rational::NegativeInf, Rational::PositiveInf);
    }

    #[test]
    fn sub_ref_ref() {
        let a = int(5);
        let b = int(3);
        assert_eq!(&a - &b, int(2));
        assert_eq!(&Rational::PositiveInf - &int(100), Rational::PositiveInf);
        assert_eq!(&Rational::NegativeInf - &int(100), Rational::NegativeInf);
        assert_eq!(&int(0) - &Rational::PositiveInf, Rational::NegativeInf);
    }

    #[test]
    #[should_panic]
    fn sub_ref_ref_undefined_panics() {
        let ni = Rational::NegativeInf;
        let _ = &ni - &ni;
    }

    // --- Mul ---

    #[test]
    fn mul_finite_finite() {
        assert_eq!(int(3) * int(4), int(12));
        assert_eq!(fin(1, 2) * int(2), int(1));
        assert_eq!(int(-2) * int(3), int(-6));
    }

    #[test]
    fn mul_inf_positive_finite() {
        assert_eq!(Rational::PositiveInf * int(5), Rational::PositiveInf);
        assert_eq!(int(5) * Rational::PositiveInf, Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf * int(5), Rational::NegativeInf);
        assert_eq!(int(5) * Rational::NegativeInf, Rational::NegativeInf);
    }

    #[test]
    fn mul_inf_negative_finite() {
        assert_eq!(Rational::PositiveInf * int(-5), Rational::NegativeInf);
        assert_eq!(int(-5) * Rational::PositiveInf, Rational::NegativeInf);
        assert_eq!(Rational::NegativeInf * int(-5), Rational::PositiveInf);
        assert_eq!(int(-5) * Rational::NegativeInf, Rational::PositiveInf);
    }

    #[test]
    fn mul_inf_inf() {
        assert_eq!(Rational::PositiveInf * Rational::PositiveInf, Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf * Rational::NegativeInf, Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf * Rational::PositiveInf, Rational::NegativeInf);
        assert_eq!(Rational::PositiveInf * Rational::NegativeInf, Rational::NegativeInf);
    }

    #[test]
    #[should_panic(expected = "+inf * 0")]
    fn mul_pos_inf_zero_panics() {
        let _ = Rational::PositiveInf * int(0);
    }

    #[test]
    #[should_panic(expected = "-inf * 0")]
    fn mul_neg_inf_zero_panics() {
        let _ = Rational::NegativeInf * int(0);
    }

    // --- MulAssign ---

    #[test]
    fn mul_assign_finite() {
        let mut a = int(3);
        a *= int(4);
        assert_eq!(a, int(12));
    }

    #[test]
    fn mul_assign_inf() {
        let mut a = Rational::PositiveInf;
        a *= int(2);
        assert_eq!(a, Rational::PositiveInf);
    }

    // --- Div ---

    #[test]
    fn div_finite_finite() {
        assert_eq!(int(6) / int(3), int(2));
        assert_eq!(int(1) / int(2), fin(1, 2));
        assert_eq!(int(-6) / int(2), int(-3));
    }

    #[test]
    fn div_finite_inf_is_zero() {
        assert_eq!(int(5) / Rational::PositiveInf, int(0));
        assert_eq!(int(-5) / Rational::NegativeInf, int(0));
        assert_eq!(int(0) / Rational::PositiveInf, int(0));
    }

    #[test]
    fn div_inf_by_positive_finite() {
        assert_eq!(Rational::PositiveInf / int(3), Rational::PositiveInf);
        assert_eq!(Rational::NegativeInf / int(3), Rational::NegativeInf);
    }

    #[test]
    fn div_inf_by_negative_finite() {
        assert_eq!(Rational::PositiveInf / int(-3), Rational::NegativeInf);
        assert_eq!(Rational::NegativeInf / int(-3), Rational::PositiveInf);
    }

    #[test]
    fn div_positive_by_zero() {
        assert_eq!(int(5) / int(0), Rational::PositiveInf);
    }

    #[test]
    fn div_negative_by_zero() {
        assert_eq!(int(-5) / int(0), Rational::NegativeInf);
    }

    #[test]
    #[should_panic(expected = "0 / 0")]
    fn div_zero_by_zero_panics() {
        let _ = int(0) / int(0);
    }

    #[test]
    #[should_panic(expected = "+inf / 0")]
    fn div_pos_inf_by_zero_panics() {
        let _ = Rational::PositiveInf / int(0);
    }

    #[test]
    #[should_panic(expected = "-inf / 0")]
    fn div_neg_inf_by_zero_panics() {
        let _ = Rational::NegativeInf / int(0);
    }

    #[test]
    #[should_panic(expected = "±inf / ±inf")]
    fn div_inf_by_inf_panics() {
        let _ = Rational::PositiveInf / Rational::PositiveInf;
    }

    // --- InfRational ---

    #[test]
    fn infrational_sub_ref_ref() {
        let a = InfRational::new(int(5), rug::Rational::from(1));
        let b = InfRational::new(int(3), rug::Rational::from(1));
        let c = &a - &b;
        assert_eq!(c.rat, int(2));
        assert_eq!(c.inf, rug::Rational::from(0));
    }

    #[test]
    fn infrational_total_order() {
        let a = InfRational::new(int(5), rug::Rational::from(0));
        let b = InfRational::new(int(5), rug::Rational::from(1)); // 5 + eps
        let c = InfRational::new(int(6), rug::Rational::from(-1)); // 6 - eps
        assert!(a < b);
        assert!(b < c);
        let mut v = vec![c.clone(), a.clone(), b.clone()];
        v.sort();
        assert_eq!(v, vec![a, b, c]);
    }
}
