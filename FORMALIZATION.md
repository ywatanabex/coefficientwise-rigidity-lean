# Formalization scope

The main Theorems A–C, including every clause listed in the
[correspondence table](README.md#correspondence-with-the-paper), are
**VERIFIED (Lean kernel checked)** through
[`manuscriptMainTheorems`](CoefficientwiseRigidity/Paper.lean).
The manuscript version is identified in [MANUSCRIPT.json](MANUSCRIPT.json).

## Machine-checked content

| Content | Evidence |
|---|---|
| Concrete coefficients, actual covers, gauges, support and feasibility | Explicit configuration bijections and polynomial coefficient identities |
| Width-two comparison, κR, 2R, odd-group 3R and sharpness | Vertex induction from actual tree decompositions, original holonomy groups and concrete C4 witnesses |
| Chordal-bipartite comparison and equality rigidity | Orders derived from induced-cycle exclusion; full increasing product cone, saturation, actual contraction and rejected configurations |
| Seam comparison, every root / actual-edge fibre, equality and every construction-piece relative deficit | Actual configuration pullbacks, positive ordinary counts and construction induction |
| Quantitative propagation of the original reserve | A designated atom occurrence, every positive real λ and explicit zero-reserve branches |
| Manuscript reserve and the all-profile coefficient polynomial bound | Shifted coefficient identity, including the negative-exponent convention; extension of B to every profile |

The development uses finite rational Newton kernels and real counting
inner-product spaces. Coefficients are integers; κ and relative deficits
are exact rationals. The local deficit proof derives its estimate from
K2 monotonicity and two-label cancellation; the paper's trace expansion
is not an imported premise. The converse direction of structural lemma
B4 is also not a main-theorem dependency.

## Auxiliary article results outside the formalization

Each row below has status **FORMALIZATION-INCOMPLETE** for the stated
additional scope. These are auxiliary statements outside the checked
main-theorem target.

| Article label | Additional scope not formalized |
|---|---|
| `cor:profilekappa` | Rank-capped κ and the singleton minimal-degree strengthening |
| `cor:dualDP`, `cor:shameful` | Formal identification with general DP covers and formalization of Dong's external theorem; that paper dependency is outside A–C |
| `prop:first` | General lowest homogeneous defect and shortest nonflat cycle formula |
| `ex:sharp` | Full polynomial equality for every even cycle; B's uniform sharpness is already checked using C4 |
| `ex:even` | The M = 6, order-two holonomy example with κ = 3 and its two DP profiles |
| `cor:polynomial`, `cor:disconnected` | Evaluation at activities and division, and the quantitative separated-component corollary; the all-profile coefficient bound is checked |
| `cor:relative` | The exact empty-seam product formula for relative deficit; the all-piece inequality and the interval [0,1] are checked |
| Structural lemma B4 and intermediate displayed formulas | Its unused converse direction and formulas not used by the Lean proof route |

Finite diagnostics have status **COMPUTATIONAL**, not VERIFIED all-size
proofs. Refuted stronger statements in [GUARDRAILS.md](GUARDRAILS.md) have
status **REFUTED-STRENGTHENING**. Universal Watanabe, U3 and the original
uniform chordal sharp 2R claim remain **OPEN**.

Here VERIFIED is accompanied by its evidence: Lean kernel checking and
the project axiom audit. It does not claim peer review or a formal proof
of every statement in the article.
