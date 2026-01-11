#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        assert!(num != 0 || den != 0);
        let mut rat = Rational { num, den };
        rat.normalize();
        rat
    }

    fn normalize(&mut self) {
        let gcd = gcd(self.num, self.den);
        self.num /= gcd;
        self.den /= gcd;
        if self.den < 0 {
            self.num = -self.num;
            self.den = -self.den;
        }
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}
