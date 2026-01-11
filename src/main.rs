mod utils;
use utils::rational::Rational;
use utils::inf_rational::InfRational;

fn main() {
    let r1 = Rational::new(3, 4);
    let r2 = Rational::new(5, 1);
    println!("Rational 1: {}", r1);
    println!("Rational 2: {}", r2);
    let mut ir1 = InfRational::new(r1, Rational::new(1, 2));
    let ir2 = InfRational::new(r2, Rational::new(3, 4));
    println!("InfRational 1: {}", ir1);
    println!("InfRational 2: {}", ir2);
}
