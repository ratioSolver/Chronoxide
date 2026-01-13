#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lit {
    x: usize,
    sign: bool,
}

impl Lit {
    pub fn new(x: usize, sign: bool) -> Self {
        Lit { x, sign }
    }

    pub fn var(&self) -> usize {
        self.x
    }

    pub fn is_positive(&self) -> bool {
        self.sign
    }
}

impl std::fmt::Display for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.sign {
            true => write!(f, "{}", self.x),
            false => write!(f, "¬{}", self.x),
        }
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit {
            x: self.x,
            sign: !self.sign,
        }
    }
}

impl std::cmp::PartialOrd for Lit {
    fn partial_cmp(&self, other: &Lit) -> Option<std::cmp::Ordering> {
        match self.x.partial_cmp(&other.x) {
            Some(std::cmp::Ordering::Equal) => self.sign.partial_cmp(&other.sign),
            ord => ord,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_and_fields() {
        let l = Lit::new(5, true);
        assert_eq!(l.x, 5);
        assert_eq!(l.sign, true);

        let l2 = Lit::new(10, false);
        assert_eq!(l2.x, 10);
        assert_eq!(l2.sign, false);
    }

    #[test]
    fn test_display() {
        let l1 = Lit::new(5, false);
        assert_eq!(format!("{}", l1), "5");

        let l2 = Lit::new(5, true);
        assert_eq!(format!("{}", l2), "¬5");
    }

    #[test]
    fn test_not() {
        let l = Lit::new(5, true);
        let not_l = !l;
        assert_eq!(not_l.x, 5);
        assert_eq!(not_l.sign, false);

        let l2 = Lit::new(10, false);
        let not_l2 = !l2;
        assert_eq!(not_l2.x, 10);
        assert_eq!(not_l2.sign, true);

        // Double negation
        assert_eq!(!(!l), l);
    }

    #[test]
    fn test_ordering() {
        let l1 = Lit::new(5, false); // 5
        let l2 = Lit::new(5, true); // ¬5
        let l3 = Lit::new(6, false); // 6

        // Compare diff x
        assert!(l1 < l3);
        assert!(l2 < l3);

        // Compare same x, diff sign
        // false < true => 5 < ¬5
        assert!(l1 < l2);

        // Equality
        let l4 = Lit::new(5, false);
        assert!(l1 == l4);
        assert!(!(l1 < l4));
        assert!(!(l1 > l4));
    }
}
