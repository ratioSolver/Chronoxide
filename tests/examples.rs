use chronoxide::Solver;
use std::fs::read_to_string;
use std::path::PathBuf;

macro_rules! test_chronoxide {
    ($name:ident, ok, [ $($path:expr),+ ]) => {
        #[tokio::test]
        async fn $name() {
            let slv = Solver::new();

            $(
                let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                p.push($path);
                assert!(slv.read(read_to_string(&p).unwrap_or_else(|_| panic!("Failed to read file: {}", $path))).await.is_ok(), "Failed to read RiDDle script from file: {}", $path);
            )+

            assert!(slv.solve().await.is_ok(), "Solver failed for test: {}", stringify!($name));
        }
    };

    ($name:ident, err, [ $($path:expr),+ ]) => {
        #[tokio::test]
        async fn $name() {
            let slv = Solver::new();
            let mut read_failed = false;

            $(
                let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
                p.push($path);
                if slv.read(read_to_string(&p).unwrap_or_else(|_| panic!("Failed to read file: {}", $path))).await.is_err() {
                    read_failed = true;
                }
            )+

            if !read_failed {
                assert!(slv.solve().await.is_err(), "Solver unexpectedly succeeded for test: {}", stringify!($name));
            }
        }
    };
}

test_chronoxide!(test_core_00, ok, ["tests/examples/core/example_00.rddl"]);
test_chronoxide!(test_core_01, ok, ["tests/examples/core/example_01.rddl"]);
test_chronoxide!(test_core_02, err, ["tests/examples/core/example_02.rddl"]);
test_chronoxide!(test_core_03, ok, ["tests/examples/core/example_03.rddl"]);
test_chronoxide!(test_core_04, ok, ["tests/examples/core/example_04.rddl"]);
test_chronoxide!(test_core_05, err, ["tests/examples/core/example_05.rddl"]);
