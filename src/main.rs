mod utils;
use utils::rational::Rational;

fn main() {
    let r1 = Rational::new(3, 4);
    let r2 = Rational::new(5, 1);
    println!("Rational 1: {}", r1);
    println!("Rational 2: {}", r2);
}
