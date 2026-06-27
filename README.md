# cut-and-project

Period formulas for one-dimensional cut-and-project gap sequences, with
explicit rational-slope formulas and the complementary irrational
aperiodicity statement formalized in Lean 4.

## Setup

For coprime $\alpha, \beta \in \mathbb{N}$ and a window parameter
$\omega \in \mathbb{R}_{\ge 0}$, the set of accepted lattice points is

$$
C = \lbrace (x, y) \in \mathbb{Z}^2 \mid y \in [\tfrac{\alpha}{\beta}(x-\omega),\,\tfrac{\alpha}{\beta}x+\omega] \rbrace.
$$

After projecting orthogonally onto $f(x) = (\alpha/\beta)x$ and
sorting, the resulting sequence of consecutive gaps
$(d^{(i)})_{i \in \mathbb{Z}}$ has minimal period $\lambda$.

## Main results

With

$$
N = \lfloor\omega\alpha\rfloor + \lfloor\omega\beta\rfloor + 1,
\qquad
D = \alpha^2 + \beta^2,
$$

counting projected points with multiplicity gives

$$
\lambda_{\mathrm{multiset}} =
\begin{cases}
N & \text{if } D \nmid N, \\
N/D & \text{if } D \mid N,
\end{cases}
$$

while discarding multiplicities gives

$$
\lambda_{\mathrm{set}} =
\begin{cases}
N & \text{if } N < D, \\
1 & \text{if } N \ge D.
\end{cases}
$$

In every case $\lambda_{\mathrm{set}}$ divides $\lambda_{\mathrm{multiset}}$
(so in particular $\lambda_{\mathrm{set}} \le \lambda_{\mathrm{multiset}}$),
with equality if and only if $N \le D$.

For positive irrational slope and strip half-width $\omega > 0$, the
projected set has no coincident projected values, and its gap sequence has
no finite period.

## Paper

- `LaTeX/rational_cut_and_project_gap_periods.tex` — main paper
  (statements, proofs, related-literature discussion, and Lean
  correspondence in Table 1).

## Companion work

The three-gap (Steinhaus) theorem — that the gaps of
$\lbrace i\alpha/\beta \bmod 1 : 0 \le i < N \rbrace$ take **at most three
distinct lengths** — is complementary to the period results here: this work
gives the *period* of the rational gap sequence, while the three-gap theorem
bounds the *number of distinct gap lengths* in a single window. A
self-contained Lean 4 / Mathlib formalization of the three-gap theorem,
uniform in the rotation number (rational and irrational alike), is given in a
companion project:
<https://github.com/dkunert/three-gap-theorem-lean>.

## Lean 4 formalization

The mathematical core is formalized in
`Lean/CutAndProject/CutAndProject/` across two files, totaling
~3,760 lines with no `sorry`, `admit`, or `axiom`:

- `Basic.lean` (~2,862 lines) — both period theorems for the
  rational case (multiset and set conventions).
- `Irrational.lean` (~896 lines) — Proposition 1 of the paper:
  for positive irrational slope and strip half-width $\omega > 0$,
  the projected gap sequence has no finite period.

The headline theorems for the rational, geometric enumeration are:

- `main_theorem_geometric_concrete` — multiset period.
- `set_main_theorem_geometric_concrete` — set period.

Both thread the geometric residue map
$c_r \equiv -\alpha\beta^{-1}r \pmod{D}$ through to the concrete
period statement. A full line-by-line correspondence between paper
results and Lean declarations is given in Table 1 of the paper.

### Architecture

The proof has two layers.

**Layer 1:** The strip geometry and projection are reduced to a
discrete enumeration of $N$ consecutive residue classes modulo $D$
under the multiplier $m = -\alpha\beta^{-1}$ (Sections 2–3 of the
paper).

**Layer 2:** Starting from the residue model, Lean
proves coprimality, residue distribution (uniform and non-uniform),
the cyclic-interval structure, the trivial stabilizer lemma, generic
minimality, the degenerate case, and the case dispatch — for both the
multiset and set conventions. The geometric multiplier is threaded
through via the `GeometricProjection` typeclass; the concrete instance
`GeometricProjectionConcrete` discharges its four axioms. The
set-valued enumeration mirrors the multiset construction with
multiplicities flattened to $\{0,1\}$.

### Reusable components (Mathlib candidates)

The rational period formula is classical; the contribution here is the
machine-checked formalization. Part of
it is general number theory, with no cut-and-project semantics, and may be of
wider use — these are the natural pieces to upstream to Mathlib:

- **Distribution of `N` consecutive residues mod `D`** (`Basic.lean`, section
  `ResidueDistribution`). With `count_hits` counting how often each class is
  hit, `residue_distribution` shows every class is hit `⌊N/D⌋` or `⌈N/D⌉` times
  with exactly `N mod D` classes attaining the larger value;
  `uniform_residue_distribution` is the `D ∣ N` case; and
  `residue_distribution_unit` shows the distribution is invariant under
  multiplying the residues by a unit of `(ZMod D)ˣ`.
- **Cyclic-interval stabilizer** (`Basic.lean`, section `Minimality`):
  `cyclic_interval_stabilizer_trivial` — a proper nonempty cyclic interval of
  residues mod `D` has trivial translation stabilizer.

The Kronecker-density and `ZMod`-unit building blocks these rest on are already
in Mathlib; a search of the Mathlib docs and Loogle did not turn up the
`ResidueDistribution` packaging itself, so it looks like a genuine contribution
candidate (to be confirmed on the Lean Zulip).

### Versions

- Lean: `leanprover/lean4:v4.29.1` (pinned in
  `Lean/CutAndProject/lean-toolchain`).
- Mathlib: `v4.29.1`, exact commit
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6` (pinned in
  `Lean/CutAndProject/lake-manifest.json`).

### Building

Install [`elan`](https://github.com/leanprover/elan) (this picks up
the pinned toolchain automatically), then:

```
cd Lean/CutAndProject
lake exe cache get   # download Mathlib build cache (recommended)
lake build
```

## Code

### C (`src/c/`)

Two C codebases compute period lengths over large parameter sweeps,
used to verify the theorems empirically.

- `src/c/multiset/` — multiset period.
- `src/c/set/` — set period.

Each subdirectory has its own `constants.h` (runtime configuration:
memory limits, $x$-range, conjecture-test counts, output formats) and
a `Makefile` with targets `make all` / `make perf` / `make debug` /
`make clean`.

> **Note:** `MAX_PERIOD_ARRAY_SIZE` controls a single allocation; the
> default of $8 \times 10^9$ requests $\approx 60$ GB of RAM. Adjust
> before building.

### Python (`src/python/`)

- `verify_paper.py` — checks both period theorems and all corollaries
  against the six-column CSVs in `tests/`. Pure stdlib, no
  dependencies. Targets: `make run` / `make clean`.
- `recompute_broken_set_periods.py` — utility that recomputes
  `period_set` for any CSV row whose value is a negative sentinel
  (i.e. an aborted C-side run). Computes the set period from the
  residue model independently of the theorem; requires `numpy`.
- `generate_set_test_file.py` — generates an independent
  set/multiset CSV (`tests/set_theorem_balanced_test.csv`) from
  Python implementations of both period algorithms.

## Provenance

The author used ChatGPT, Gemini, and Claude as AI assistants during
mathematical exploration, drafting, proof construction, and the
creation of the Lean formalization, all under the author's direction.
The author has independently verified the mathematical content and
accepts full responsibility for the results and any errors. The
correctness of the Lean formalization rests not on this provenance but
on the Lean 4 kernel: anyone can rebuild it and inspect the axiom list
(no `sorry`, `admit`, or `axiom`).

## License

MIT — see [`LICENSE`](LICENSE). © 2026 Dirk Kunert.
