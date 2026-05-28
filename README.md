# rank-of-matrix

Lean 4 project exploring a sparse-matrix encoding and a computable rank procedure,
with a target correctness theorem connecting the implementation to Mathlib's
`Matrix.rank`.

## Project Goals

- Define a sparse matrix representation suitable for row operations.
- Implement rank-style elimination steps (swap, scale, combine rows).
- Define a computable rank function.
- Prove correctness against Mathlib's dense matrix rank.

## Repository Structure

- `RankOfMatrix/Basic.lean`: main sparse representation and rank work.
- `RankOfMatrix.lean`: library entry point.
- `Main.lean`: executable entry point.
- `lakefile.toml`: Lake project configuration.

## Prerequisites

- Lean 4 with Lake (via `elan`).
- Internet access for the first `lake update`/build (to fetch Mathlib).

## Setup

```bash
lake update
lake build
```

## Common Commands

```bash
# Build everything
lake build

# Run the executable target from Main.lean
lake exe rank-of-matrix

# Open Lean file checks (editor does this automatically)
lake env lean RankOfMatrix/Basic.lean
```

## Current Status

- Sparse matrix type is defined.
- Conversion to dense `Matrix (Fin m) (Fin n) K` is scaffolded.
- Elimination and correctness proof are in progress.

## Push to GitHub

```bash
git add .
git commit -m "Initial commit"
git branch -M main
git remote add origin https://github.com/<your-username>/rank-of-matrix.git
git push -u origin main
```

If `origin` already exists:

```bash
git remote set-url origin https://github.com/<your-username>/rank-of-matrix.git
git push -u origin main
```