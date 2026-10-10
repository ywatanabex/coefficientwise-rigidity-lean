# Coefficientwise rigidity: Lean formalization

Lean 4 formalization of **all clauses of the main Theorems A–C** of

> Yusuke Watanabe, *Coefficientwise Extremality and Rigidity for Independent Sets in Bipartite Graph Covers*.

The formalization status is **VERIFIED (Lean kernel checked)** for these
main theorems. [FORMALIZATION.md](FORMALIZATION.md) records the precise
scope and auxiliary article results that are not yet formalized.

The publication entry point is
[`CoefficientwiseRigidity/Paper.lean`](CoefficientwiseRigidity/Paper.lean):

```lean
CoefficientwiseRigidity.manuscriptMainTheorems :
  CoefficientwiseRigidity.ManuscriptMainTheorems
```

The proof counts actual configurations in finite graph covers. It proves
their correspondence with independent-set polynomial coefficients and
derives the structural hypotheses from tree decompositions or induced-cycle
exclusion. [PAPER_PROOF.md](PAPER_PROOF.md) explains the proof routes.

## Reproduce the proof

Install [elan](https://github.com/leanprover/elan) and Git, then run the
following commands from this repository's root:

```sh
lake exe cache get
lake build
```

The first command obtains the pinned mathlib dependency cache. The second
checks the proof library and `PaperAudit`. Dependency acquisition requires
network access; all project proof sources are in this repository.

- Lean: `leanprover/lean4:v4.17.0-rc1`, fixed by [lean-toolchain](lean-toolchain).
- mathlib: `5e2e7342a4a0ce726951b40d00a9a4311ba5e447`.
- Every transitive dependency revision is fixed by [lake-manifest.json](lake-manifest.json).

`PaperAudit.lean` checks the transitive axiom dependencies of every
kernel-safe declaration in the `CoefficientwiseRigidity` namespace,
including definitions and theorem statements. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed. It rejects `sorryAx`,
custom axioms and native-evaluation axioms. The sharpness counts also use
kernel `decide`.

For a clean rebuild, a fresh audit and independent finite diagnostics,
install Python 3.10 or later and run:

```sh
python3 checks/validate_paper.py --clean
```

The script needs only the Python standard library. It works from any
working directory and does not require a Git commit or a sibling
repository. It writes a validation receipt and logs to the ignored
`validation/` directory. To skip the optional finite diagnostics, use
`--lean-only`; these diagnostics have status `COMPUTATIONAL` and are never
proof premises.

[The GitHub Actions workflow](.github/workflows/lean.yml) obtains the pinned
dependencies and runs the same clean validation command on a fresh
checkout.

## Correspondence with the paper

All declaration names below are in the `CoefficientwiseRigidity` namespace.
The formal hypotheses remain explicit in their Lean statements.

| Paper statement | Lean declaration and scope |
|---|---|
| A: coefficient comparison and equality iff flatness on the positive support | `paperMainA`; treewidth at most two or chordal bipartite, every feasible profile, M ≥ 1 |
| B: κR deficit, R > 0, κ ≥ 2 and κ ≥ 3 for odd-order holonomy | `mainBKappa`, `mainBTwo`, `mainBOdd`; connected nonflat width-two covers, positive feasible profiles |
| B: sharpness of the uniform constants two and three | `paperMainBSharpness`; actual C4 covers with D = 2R and D = 3R, R = 1; the latter has holonomy order three |
| C(i): coefficient and legal root / actual-edge fibre comparison | `paperMainCComparisonRigidity`, `paperMainCFibres` |
| C(ii): equality iff active flatness | `paperMainCComparisonRigidity` |
| C(ii): relative deficit of every atom and intermediate construction occurrence | `paperMainCRelative`; occurrences tracked by `ConstructionPiece` |
| C(iii): propagate a designated atom's λR bound with the original reserve | `paperMainCQuantitativeReal`; every positive real λ, M ≥ 2, positive feasible profiles |
| All main Theorems A–C together | `manuscriptMainTheorems` |
| All-profile coefficient form of the polynomial κ bound | `coefficient_kappa_paperReserve`; includes zero occupations and infeasible profiles |

Coefficients are configuration cardinalities, without factorial
normalization. `paperReserve_eq_polynomial_coefficient` proves that the
manuscript reserve equals `[x^a](x^V p_G^(M−2))` on every profile, with the
paper's negative-exponent convention. Relative deficits use exact rational
ratios with positive denominators.

## Paper version

The manuscript is not yet published; an arXiv submission is planned.
The identifier and version are pending. [MANUSCRIPT.json](MANUSCRIPT.json) identifies
the manuscript used for this correspondence by its exact SHA-256 digest.
The paper source and PDF are not required to build these proofs.

When the manuscript receives an arXiv version, record that version and its
URL in `MANUSCRIPT.json` and here, and associate it with the corresponding
code release.

## Contents

- `CoefficientwiseRigidity/`: all proof modules, including `Paper.lean`.
- `CoefficientwiseRigidity.lean`: aggregate proof library.
- `PaperAudit.lean`: default-build axiom audit.
- `PAPER_PROOF.md`, `FORMALIZATION.md` and `GUARDRAILS.md`: proof guide, scope and necessary boundaries.
- `checks/`: standalone validator and independent finite diagnostics with their local helper modules.
- `.github/workflows/lean.yml`: automated clean build and validation.

The target is finite simple bipartite bases in the stated structural
classes and their certified seam compositions. The universal bipartite
Watanabe conjecture, general U3 and a uniform sharp 2R bound for every
chordal-bipartite cover remain **OPEN**.

## License

The project sources and documentation are licensed under the
[MIT license](LICENSE). Downloaded dependencies retain their own licenses.
