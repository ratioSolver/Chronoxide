use chronoxide::Solver;

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() < 2 {
        eprintln!("Usage: {} <files>", args[0]);
        std::process::exit(1);
    }

    let files = &args[1..];

    let (slv, _rx) = Solver::new();
    for file in files {
        slv.read(&std::fs::read_to_string(file).expect("Failed to read file"));
    }
}
