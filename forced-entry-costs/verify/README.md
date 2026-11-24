# Verification scripts

Consistency checks for the paper *Forced-Entry Costs at a Fixed Optimal Assignment under Paired Interval
Uncertainty*. They are **not proofs**: they test the statements on small and random instances. The formal proof of
Theorem 2 is in [`../lean/`](../lean/).

The construction of Section 2 of the paper was implemented independently four times; each directory is
self-contained and shares no code with the others.

| Directory | Written from | Arithmetic |
|---|---|---|
| `implementation_a/` | a written description of the construction | exact rationals for the assignment values; floating point (HiGHS) for linear programs |
| `implementation_b/` | Section 2 of the paper | exact rationals; floating point for linear programs |
| `implementation_c/` | Section 2 of the paper | exact integers |
| `implementation_d/` | Section 2 of the paper | exact integers; floating point for linear programs |

Requirements: Python 3 with `numpy` and `scipy` (`networkx` is used by one script if present). Recorded with
Python 3.13.18, NumPy 2.5.3, SciPy 1.18.1, NetworkX 3.7. Random seeds are fixed in the files. Run each script from
its own directory, for example `cd implementation_a && python3 test_adapter.py`. The files `*.out` are the outputs
of the recorded run (24 November 2026, 4 cores); every script ended with exit code 0. Scripts also write small
`*_results.json` files when run.

| Script | What it checks | Recorded time |
|---|---|---|
| `implementation_a/test_adapter.py` | Theorem 2 on the diamond family with `n <= 3` (all corner scenarios, sampled interior ones) and on 60 random directed acyclic graphs: identity optimal and unique among permutations, dual certificate, forced value = route formula, `eta_e`; four instances with `N <= 9` by enumeration of all permutations | 39 s |
| `implementation_a/test_adapter_n45.py` | the same per-scenario checks for `n = 4, 5` (`N = 125, 196`), sampled scenarios; floating-point assignment solver on integer-scaled matrices | 14 s |
| `implementation_a/test_extra_dag.py` | one explicit graph with parallel arcs, a dead end and repeated interactions; all 729 scenarios of a grid | 6 s |
| `implementation_a/test_scope.py` | outside the box the identity need not be optimal; further scope checks | 2 s |
| `implementation_a/test_prop1.py` | Proposition 1 by enumeration on 400 random instances with `N <= 4`; control: with one parameter shared across `F` the formula fails | 1 s |
| `implementation_a/test_pafp.py` | the reduction in the proof of Corollary 4 on 40 random instances | 3 s |
| `implementation_a/test_sparse.py` | Corollary 8: dimension `7n + 1 + 16|E|` and value formula on 10 instances | 3 s |
| `implementation_a/test_upper.py` | Proposition 9: the two linear programs agree on 40 random graphs; exact forced value at the maximising scenario; the fixed polyhedron with `4n^2` inequalities for `n = 2, 3` | 2 s |
| `implementation_a/test_B.py` | Section 4 on tiny cases: algebraic identities, the covering lemma by enumeration for `n <= 4`, Lemma 19 and the probing weights for `n = 2` | 260 s |
| `implementation_a/test_C.py`, `test_C2.py` | Sections 5 and 6: the inequalities of Theorem 11 for `n <= 6`, the entropy and rounding step, the estimates of Proposition 22; crossover of sizes | 5 s, 6 s |
| `implementation_b/construct_check.py` | Theorem 2 and the lemmas of Section 2 on 36 random graphs and on tiny instances by enumeration; the formula in the proof of Corollary 3 for all graphs on at most three vertices | 90 s |
| `implementation_b/numbers_check.py` | identities and constants of Sections 3 to 6 | 2 s |
| `implementation_c/check_A.py 200` | the reduction in the proof of Corollary 4 on 210 instances, with `M = 2^N` | 38 s |
| `implementation_c/check_BCDFI.py` | Remark 21, the end of the proof of Proposition 22, the arithmetic of the paragraph on relative error, Proposition 1, Remark 23 | 2 s |
| `implementation_d/item1_prop_indep.py`, `item1b_controls.py` | Proposition 1 on 1500 instances; the sign condition is necessary (mixed-sign variant of the construction) | 73 s, 1 s |
| `implementation_d/item2_cor_tw.py` | Corollary 8 on 11 graphs with `n <= 5`; the affine bijection with the correlation polytope of the graph | 69 s |
| `implementation_d/item3_prop_upper.py` | Proposition 9: both linear programs against enumeration, graphs with dead ends and unreachable vertices, the fixed polyhedron for `n <= 3` | 7 s |

`adapter.py` and `adapter_sec2.py` are the modules with the construction used by the scripts of their directory.

Comments inside the scripts of directories `b`, `c` and `d`, and the lines they print, sometimes refer to results
by the numbers they had in earlier drafts of the paper or by working labels ("Item A", "Item 1"); the table
above uses the numbering of the published version and is authoritative.
