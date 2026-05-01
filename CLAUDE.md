# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Mathematical research project investigating period lengths of one-dimensional cut-and-project sequences. The project has two implementations:
- **C** (`src/c/multiset/`): High-performance computation for testing mathematical conjectures
- **Python** (`src/python/`): Statistical analysis and ML modeling of computed results
- **LaTeX** (`LaTeX/`): Academic paper source and compiled PDF

## Build & Run Commands

### C Implementation

```bash
cd src/c/multiset
make all        # Build both performance (cnp) and debug (cnp_debug) versions
make perf       # Build optimized version only (-O3 -flto -funroll-loops -ffast-math)
make debug      # Build debug version only (-O0 -g)
make clean      # Remove binaries and object files
./cnp           # Run performance version
./cnp_debug     # Run debug version
```

### Python Implementation

```bash
cd src/python
make run        # Run verify_paper.py against tests/*.csv (Python stdlib only, no venv needed)
make clean      # Remove venv and __pycache__
```

## Configuration Before Running C Code

Edit `src/c/multiset/constants.h` before building/running:

- `X_MIN`, `X_MAX`: x-interval for computation (default: 0 to 1,000,000)
- `NUMBER_OF_CONJECTURE_TESTS`: Number of random test iterations (default: 1000)
- `TASKS`: Bitwise flags — `TEST | TEST_CONJECTURES` (both enabled by default)
- `CREATE_FILE_TO_FIND_A_PATTERN`: Set to `true` to generate CSV output (default: `false`)
- `MAX_PERIOD_ARRAY_SIZE`: Controls memory allocation (~8GB at default of 8,000,000,000)

## Architecture

### C Code Structure

**`main.c`** — Entry point: allocates aligned memory (`dx` array), then dispatches to `test()` and/or `test_conjectures()` based on `TASKS` flags.

**`mathematics.h` / `mathematics.c`** — Core algorithm. Key types:
- `number_t` (`int_fast64_t`): Primary integer type
- `rational_t`: Struct with `numerator`/`denominator` fields

Key functions:
- `lambda(α, β, γ, δ, x_min, x_max, sort, dx)`: Core computation — iterates x in [x_min, x_max], finds valid y integers, computes Euclidean distances, then finds period length
- `find_period_length()`: Brute-force period detection
- `dx_alloc()`: Allocates aligned memory for distance arrays
- Rational arithmetic: `rational_add`, `rational_subtract`, `rational_floor`, `rational_ceil`, `shorten`

**`test.c`** — Unit tests for GCD, rational arithmetic, and period-finding logic.

**`conjectures.c`** — Tests all 6 mathematical conjectures using random α, β (coprime) and γ, δ (ω ratio) values.

### Python Code Structure

**`verify_paper.py`** reads CSVs from `tests/` and verifies Theorem 3.1 and Corollaries 5.1–5.5 of `LaTeX/rational_cut_and_project_gap_periods.tex`. Defaults to `../../tests/new_find_patterns_x_max_1000000_51012_lines.csv` and `../../tests/degenerate_patterns_5000_lines.csv`. Pure stdlib — no external dependencies.

Earlier exploratory scripts (`main.py` with XGBoost / OLS / curve-fit, `anomaly.py`, `test_conjecture_7.py`, plus the older 70 977-line dataset) are archived under `LaTeX/support/src/`.

### Data Flow

C program → CSV file (`tests/*.csv`) → `verify_paper.py` → pass/fail report against the paper's claims.

The C program can generate the pattern CSV by setting `CREATE_FILE_TO_FIND_A_PATTERN true` in `constants.h`.

## Mathematical Context

The project studies cut-and-project sequences defined by coprime α, β ∈ ℕ, parameter ω ≥ 0, and an x-interval. Points are projected onto f(x) = (α/β)x, Euclidean distances are computed, and the period length λ is determined. The 6 conjectures relate λ to Λ_{α,β} (a reference period) depending on the value of ω.
