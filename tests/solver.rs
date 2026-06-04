use chronoxide::solver::Solver;
use std::{fs::read_to_string, path::PathBuf};

macro_rules! test_chronoxide {
    ($name:ident, $($path:expr),+) => {
        #[tokio::test]
        async fn $name() {
            let solver = Solver::new();
            $(
                let mut full_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                full_path.push($path);
                let content = read_to_string(&full_path).expect(&format!("Failed to read file: {}", $path));
                solver.read(content).await.expect("Failed to read problem");
            )+
            solver.solve().await.expect("Failed to solve the problem");
        }
    };
}

macro_rules! test_inconsistent {
    ($name:ident, $($path:expr),+) => {
        #[tokio::test]
        async fn $name() {
            let solver = Solver::new();
            $(
                let mut full_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                full_path.push($path);
                let content = read_to_string(&full_path).expect(&format!("Failed to read file: {}", $path));
                solver.read(content).await.expect("Failed to read problem");
            )+
            assert!(solver.solve().await.is_err(), "Expected the problem to be inconsistent, but it was solved successfully");
        }
    };
}

test_chronoxide!(test_core_00, "tests/examples/core/example_00.rddl");
test_chronoxide!(test_core_01, "tests/examples/core/example_01.rddl");
test_chronoxide!(test_core_02, "tests/examples/core/example_02.rddl");
test_chronoxide!(test_core_03, "tests/examples/core/example_03.rddl");
test_chronoxide!(test_core_04, "tests/examples/core/example_04.rddl");
// test_inconsistent!(test_core_05, "tests/examples/core/example_05.rddl");
// test_inconsistent!(test_core_06, "tests/examples/core/example_06.rddl");
