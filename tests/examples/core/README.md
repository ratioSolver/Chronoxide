# Core Examples

This folder contains the minimal RiDDLe examples used to exercise the core grammar and runtime behavior.

## Contents

- `example_00.rddl` to `example_13.rddl`: progressively richer scenarios for parsing and semantic checks.

## Purpose

Use these files to:

- validate parser coverage on essential syntax,
- debug changes in expression/statement handling,
- quickly reproduce regressions with small inputs.

## How To Run

From the repository root:

```bash
cargo test --test examples test_core_
```

To run all integration examples:

```bash
cargo test --test examples
```