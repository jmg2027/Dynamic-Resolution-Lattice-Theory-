//! `Monomial { coeff, x_pow, y_pow }` representing `coeff · x^p · y^q`.

use num_bigint::BigUint;

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Monomial {
    pub coeff: BigUint,
    pub x_pow: u64,
    pub y_pow: u64,
}

impl Monomial {
    pub fn one() -> Self {
        Self { coeff: BigUint::from(1u32), x_pow: 0, y_pow: 0 }
    }
    pub fn x() -> Self {
        Self { coeff: BigUint::from(1u32), x_pow: 1, y_pow: 0 }
    }
    pub fn y() -> Self {
        Self { coeff: BigUint::from(1u32), x_pow: 0, y_pow: 1 }
    }
    pub fn from_const(c: BigUint) -> Self {
        Self { coeff: c, x_pow: 0, y_pow: 0 }
    }

    pub fn mul(&self, o: &Monomial) -> Monomial {
        Monomial {
            coeff: &self.coeff * &o.coeff,
            x_pow: self.x_pow + o.x_pow,
            y_pow: self.y_pow + o.y_pow,
        }
    }

    pub fn pow(&self, n: u64) -> Monomial {
        if n == 0 { return Monomial::one(); }
        let mut acc = self.clone();
        for _ in 1..n { acc = acc.mul(self); }
        acc
    }

    pub fn eval_at(&self, x: &BigUint, y: &BigUint) -> BigUint {
        let mut r = self.coeff.clone();
        for _ in 0..self.x_pow { r *= x; }
        for _ in 0..self.y_pow { r *= y; }
        r
    }
}
