# Lean 4 proof of the exact adapter theorem

A self-contained Lean 4 project (pinned toolchain, pinned Mathlib, one check command) that
machine-checks **Theorem 2 (exact adapter)** of

> F. Majchrzak, *Forced-Entry Costs at a Fixed Optimal Assignment under Paired Interval
> Uncertainty: a Lean-Verified Exact Reduction and Its Consequences for Linear Programs* (2026).

The theorem is checked in full: the dimension of the assignment instance, conditions
(C1)–(C4), the formula for the forcing cost `h_e(θ)` in every scenario of the box, and the
formula for its lower endpoint `η_e`. The project also contains a formalisation of a known
result which the paper imports, the covering inequality of Kaibel and Weltge.

Nothing else of the paper is formalised. In particular the statements on linear programs and
the corollaries are **not** machine-checked; see "What is NOT proved here".

The project has twelve modules (3907 lines):

* `DagCycleAssignment`, `SubdivisionAssignment`: permutations supported on the arcs of an
  acyclic graph and one return arc; the subdivided graph;
* `AdapterCost`, `AdapterFeatures`, `AdapterBounds`, `AdapterBirkhoff`, `AdapterPaths`,
  `AdapterTheorem`, `AdapterPattern`, `AdapterMain`, `AdapterComplements`: the cost matrix of
  the adapter, defined on all ordered pairs of vertices, and the proof of Theorem 2;
* `CorrelationCoverKernel`: the covering inequality (independent of the other modules).

| Pin | Value |
| --- | --- |
| Lean | `4.19.0` (commit `6caaee842e94`), see `lean-toolchain` |
| Mathlib | commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, see `lakefile.toml`, `lake-manifest.json` |
| kernel replay tool | `lean4checker` tag `v4.19.0` (commit `e11f65c651edd58d68ba260015d2bfde5102cd7f`), a Lake dependency |

These are the versions the modules were written for; they are not the newest ones.

## How to check

Requirements: [elan](https://github.com/leanprover/elan), git, about 6.5 GB of free disk space.

```bash
lake exe cache get        # pre-built Mathlib for the pinned commit
./scripts/check.sh        # prints "OK: build, 57 axiom reports, kernel replay of 12 modules"
```

`scripts/check.sh` runs, and fails if any step fails:

1. `lake build` of the twelve modules;
2. a scan of the sources for `sorry`, `admit`, `axiom`, `native_decide`;
3. `scripts/PrintAxioms.lean`: for 57 theorems every axiom used must be one of `propext`,
   `Classical.choice`, `Quot.sound`;
4. `lean4checker` (replay of every declaration in the Lean kernel) on the twelve modules.

During the build, three modules print the axiom reports written at their ends; these are
information messages. A record of a clean-room run is in `VERIFICATION_CLEANROOM.txt`.

## Theorem 2 (exact adapter): `AdapterMain.lean`, `exact_adapter`

### Notation of the paper and of the Lean files

| Paper | Lean |
| --- | --- |
| directed graph `D = (V, A)`, parallel arcs allowed | finite types `V`, `A`; `tail head : A → V` |
| `D` is acyclic | a rank `V → Fin N` that increases along every arc |
| interaction `(a_j, b_j)`, `j ∈ J` | finite type `J`; `arcA j`, `arcB j` |
| `α_a`, `β_j` | `α a`, `β j` |
| `ϱ`, the cost of the return arc `e = (t, s)` | `δ` |
| `Γ`, the cost of a completion entry | `H` |
| the box `Θ = ∏ [0, β_j]` | `InBox β θ` |
| vertices of the subdivided graph `D′` | `Vertex V A (chainLength arcA arcB)`, that is `V ⊕ Σ a, Fin (chainLength a + 1)` |
| `p_a` | internal vertex `0` of the chain of `a` |
| `f_j`, `f_j′` | `firstV (j, true)`, `secondV (j, true)` |
| `g_j`, `g_j′` | `firstV (j, false)`, `secondV (j, false)` |
| the two uncertain entries of `j`: `(f_j, f_j′)` and `(g_j, g_j)` | `(uRow p, uCol p)` for the two *incidences* `p = (j, true)` (the arc `a_j`, called the A-feature) and `p = (j, false)` (the arc `b_j`, the B-feature) |
| `C(θ)` | `adapterCost tail head arcA arcB s t α β θ δ H` |
| `F` (the identity) | `Equiv.refl _` as a permutation, `1` as a matrix |
| `C · X`; `C · σ` for a permutation `σ` | `dot C X`; `permCost C σ` (`dot_one`: `dot C 1 = ∑ x, C x x`, the cost of the identity) |
| doubly stochastic matrices | `doublyStochastic ℝ _` of Mathlib |
| designated entry | an arc of `D′` (`Edge`) or the return entry; `Designated` for a permutation |
| `s`–`t` path `P` of `D` | a list of arcs `l` with `IsWalk tail head s t l` (a walk; in an acyclic graph every walk is a path) |
| `[a ∈ P]` | `ind l a`, which is `1` if `a ∈ l` and `0` otherwise |
| `Q(P)` | `quadCost arcA arcB α β l` |

### Input

Finite types `V` (vertices), `A` (arcs), `J` (interactions); `tail head : A → V` (parallel arcs
are different arcs); `arcA arcB : J → A`, the two arcs of an interaction; terminals `s t`; arc
costs `α`; interaction weights `β`; the cost `δ` of the return entry; the completion cost `H`.

### Hypotheses

* `Hyp s t α β δ H`: `s ≠ t`, `α a ≥ 0`, `β j ≥ 0`, `δ > 0`, `H ≥ δ + ∑ α + 2 ∑ β + 1`;
* a rank `V → Fin N` that increases along every arc. This is how acyclicity is stated; that a
  finite acyclic graph has such a rank (a topological order) is standard and is not formalised;
* at least one path from `s` to `t` (`∃ l, IsWalk tail head s t l`).

Not assumed: that the two arcs of an interaction are different.

### The instance

Rows and columns are the vertices of the subdivided graph,
`Vertex V A (chainLength arcA arcB)`. The cost matrix in the scenario `θ : J → ℝ` is
`adapterCost … θ …`, defined on all pairs of vertices (see `AdapterCost.lean`,
`AdapterFeatures.lean`). The supplied assignment `F` is the identity; the observed entry is
`(t, s)`. A path of the original graph is a list of arcs `l` with `IsWalk tail head s t l`, and

```
pathCost θ l = ∑_{a ∈ l} α a + ∑ j, (θ j · [arcA j ∈ l] + (β j − θ j) · [arcB j ∈ l])
quadCost l   = ∑_{a ∈ l} α a + ∑ j, β j · [arcA j ∈ l] · [arcB j ∈ l]
```

### Conclusions

The Lean statement is `exact_adapter` in `AdapterMain.lean`; it is one conjunction, and the
list below follows it clause by clause. The names are the separate theorems.

1. *Dimension* (`card_vertex`): the instance has `|V| + |A| + 4 |J|` rows and columns.
2. *(C2)* (`adapterCost_affine`, `uRow_eq_uCol_iff`): for all vertices `x, y` and every real `θ`,
   `C θ x y = C 0 x y + ∑ over incidences p = (j, side) of θ j · [x = uRow p ∧ y = uCol p]`.
   So `θ j` occurs in exactly the entries of its two incidences, with coefficient `1`: the entry
   `(f_j, f_j′)`, which is not diagonal, and the diagonal entry `(g_j, g_j)`.
3. *(C3)* (`uRow_injective`, `uCol_injective`): the `2 |J|` uncertain entries have pairwise
   different rows and pairwise different columns.
4. For every scenario `θ` in the box `0 ≤ θ j ≤ β j`:
   * *(C4)* (`adapterCost_nonneg`): every entry is nonnegative;
   * *(C1), certificate* (`dual_certificate`): with row prices `dualRow θ` (`θ j` at `g_j`, `0`
     elsewhere) and zero column prices, the dual constraints hold for all pairs, with equality
     on the diagonal, and the dual objective equals the cost of the identity;
   * *(C1), uniqueness* (`identity_unique_optimal`): every doubly stochastic matrix other than
     the identity matrix costs strictly more than the identity;
   * *the forcing cost* `h_e(θ)` (`adapter_forced_value`): the least value of `C θ · (X − F)`
     over the doubly stochastic matrices `X` with `X t s = 1` exists and equals
     `δ +` the least `pathCost θ l` over the paths `l` from `s` to `t` of the original graph.
5. *The lower endpoint* `η_e` (`adapter_eta`): the least value of `C θ · (X − F)` over all
   scenarios of the box and all doubly stochastic `X` with `X t s = 1` exists and equals
   `δ +` the least `quadCost l` over the paths `l` from `s` to `t` of the original graph.

"Least value … exists and equals" is stated as: there is a real `m` that is the least element
(`IsLeast`) of both sets of values.

That the dual prices are affine in `θ`, which (C1) also requires, is the separate theorem
`dualRow_affine` (`AdapterComplements.lean`):
`dualRow θ x = ∑ over incidences p = (j, side) of θ j · [x = uRow p ∧ x = uCol p]`.
By `uRow_eq_uCol_iff` only the B-incidences contribute, so this is `∑ j, θ j · [x = g_j]`.

### Where the steps of the paper's proof are

| Paper | Lean |
| --- | --- |
| the construction | `Vertex`, `Edge` (`SubdivisionAssignment`); `cost` (`AdapterCost`); `chainLength`, `stepCost`, `diagCost`, `adapterCost` (`AdapterFeatures`) |
| Lemma on paths | acyclicity of `D′`: `edge_increases_rank`; the correspondence with the paths of `D`: `walk_of_designated`, `exists_designated_of_walk` (`AdapterPaths`), `route_of_path_unique`, `path_of_route_unique` (`AdapterComplements`); a chain is used as a whole or not at all: `whole_chain_forced` |
| Lemma on permutations | `designated_iff_identity_or_path` (`DagCycleAssignment`), `designated_iff_original_rank` (`SubdivisionAssignment`): a permutation supported on designated entries is the identity or the cycle of one simple path and the return arc, and conversely |
| Lemma (cost identity) | `adapter_cost_designated`, `adapter_cost_path`, `adapter_cost_route` (`AdapterFeatures`), `relcost_eq_pathCost` (`AdapterTheorem`), for every real `θ`; the bounds: `designated_cost_bounds` (`AdapterBounds`) |
| Lemma (completion) | `cost_completion` (`AdapterCost`), `completion_cost` (`AdapterBounds`) |
| Lemma (dual certificate) | `dual_certificate`, `identity_optimal` (`AdapterBounds`), `dualRow_affine` (`AdapterComplements`) |
| proof of Theorem 2, the step through Birkhoff's theorem | `identity_unique_optimal`, `exists_perm_le_of_entry_one` (`AdapterBirkhoff`); `face_attains`, `face_lower`, `adapter_forced_value` (`AdapterTheorem`) |
| proof of Theorem 2, the minimum over the scenarios | `pair_lower`, `pair_attained`, `adapter_min_over_scenarios` (`AdapterFeatures`); `adapter_eta` (`AdapterTheorem`) |
| (C2), (C3) | `adapterCost_affine`, `uRow_eq_uCol_iff`, `uRow_injective`, `uCol_injective` (`AdapterPattern`) |
| (C4) | `adapterCost_nonneg` (`AdapterBounds`) |
| Theorem 2 | `exact_adapter` (`AdapterMain`) |

Birkhoff's theorem is taken from Mathlib (`exists_eq_sum_perm_of_mem_doublyStochastic`).

**The correspondence between paths and permutations is a bijection** (`AdapterComplements.lean`).
Call a *route* a permutation supported on designated entries that selects the return entry.
Every path from `s` to `t` of the original graph has exactly one route that uses exactly the
chains of its arcs (`route_of_path_unique`), and every route has exactly one path whose arcs
are exactly the arcs whose chains it uses (`path_of_route_unique`). In Lean the correspondence
is stated between the paths of `D` and the routes directly; the paths of `D′` appear as the
simple paths of `designated_iff_original_rank`.

The cost identity is algebraic: it holds for every real `θ` and needs no sign assumption. The
box and `β ≥ 0` enter in the minimum over scenarios; nonnegativity of `α`, `δ` and the size of
`H` enter in the completion bound and in the dual certificate.

## `CorrelationCoverKernel.lean`: the covering inequality of Kaibel and Weltge

Words of length `n` over `{zero, a, b}`; `cross n x y` counts the positions where `x` has `a` and
`y` has `b`. A family `R` is `Valid` if `cross n x y ≠ 1` for all `x, y ∈ R`.

* `valid_card_le`: a valid family has at most `2 ^ n` words.
* `covering_inequality`: if a list of `r` valid families covers all words, then
  `3 ^ n ≤ r * 2 ^ n`.

This formalises a known argument (V. Kaibel, S. Weltge, *A short proof that the extension
complexity of the correlation polytope grows exponentially*, Discrete Comput. Geom. 53 (2015);
the induction in the proof of Theorem 1 of arXiv:1307.3543v6). It is not a new result.

## What is NOT proved here

* One auxiliary sentence of the Lemma on paths, that every new vertex has exactly one entering
  and one leaving arc in `D′`, is not a Lean statement. Its consequences that the proof uses
  are (`whole_chain_forced` and the theorems on paths and routes above).
* Everything on linear programs: the lemma that values force a face, the passage from a linear
  program to a covering by valid families, and the theorems on exact size, bounded positive
  weights, fixed additive error and fixed relative error. Of this part only the combinatorial
  covering inequality above is formalised; no polyhedral statement is.
* The corollaries (NP-hardness, no approximation in general, sparse interactions) and the two
  propositions (no parameter shared across `F`; the upper endpoint).
* The diamond family and its relation to the correlation polytope.
* Lean certifies the theorem for the definitions in these files. That the definitions
  (`cost`, `adapterCost`, `IsWalk`, `pathCost`, `quadCost`, `dualRow`, `uRow`, `uCol`) say what
  the paper means is a matter of reading them; this reading has not been reviewed externally.
  Three cross-checks are formal: `card_vertex`, `cost_completion`, and
  `adapterCost_feature_arc` / `adapterCost_feature_diag`.

## What is trusted

* The Lean 4 kernel and the three standard axioms `propext`, `Classical.choice`, `Quot.sound`.
  No other axiom is used by the 57 reported theorems; no `sorry`, `admit` or `native_decide`
  occurs in the sources.
* Mathlib as distributed for the pinned commit. Its compiled files are downloaded by
  `lake exe cache get`. The kernel replay covers the twelve modules of this project, not
  Mathlib; in particular Mathlib's proof of the Birkhoff–von Neumann theorem is used and not
  replayed here.
* The tools: Lake and `lean4checker`.

## Authorship and licence

Author and responsible person: Filip Majchrzak. The Lean code was produced by AI systems
working under the author's direction: the modules `DagCycleAssignment`,
`SubdivisionAssignment` and `CorrelationCoverKernel` were written by an AI operator of the
SAPIO MORPHEUS project based on OpenAI models; the nine `Adapter*` modules, the project files
and the clean-room record were written by AI agents based on Anthropic's Claude.

Licence of the code: Apache-2.0.
