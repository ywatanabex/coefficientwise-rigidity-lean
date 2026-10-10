# Necessary boundaries

The following stronger assertions have status **REFUTED-STRENGTHENING**.
They explain why the stated hypotheses matter. They are not
counterexamples to the Watanabe conjecture.

| Failed extension | Witness and reproducible source |
|---|---|
| Equality forces full flatness even when some ranks vanish | A swapped edge on K2,2 at M = 2 has zero deficit at (0,0,1,1), and deficit two at (1,1,1,1). Active support, rather than full-cover flatness, is needed. `checks/check_saturation.py` |
| Parallel labels may be discarded during contraction | A tight-star contraction can retain incompatible parallel constraints with zero configurations, while its identity representative is flat with two. `checks/check_star_contraction.py` |
| Nonflatness forces strict comparison at every root pin | C4, M = 3, singleton ranks, one transposition: Z = 16, P = 18, while both fixed-colour root fibres equal six. `checks/check_main_c.py` |
| An alpha leaf in the original row family is enough for nest elimination | Rows {0,1}, {0,2}, {1,2}, {0,1,2} have alpha leaves but no nest point. The Lean declarations `Structure.triangleWithFull_alpha`, `triangleWithFull_no_nest` and `triangleWithFull_not_hereditary` preserve the witness. |
| Copy amplification works for arbitrary nonadjacent pairs, or zero copies count as one | Gluing length-three paths at both ends creates an induced C6. Zero copies retain the boundary, which can have multiple configurations. `checks/check_replicas.py` |

`python3 checks/validate_paper.py --clean` runs the main-C pin control along
with finite seam and sharpness diagnostics. The other standalone checkers
can be run directly. Their outputs have status **COMPUTATIONAL** and do
not serve as premises of the Lean proofs.

Current theorem scope is in [README](README.md) and
[FORMALIZATION.md](FORMALIZATION.md).
