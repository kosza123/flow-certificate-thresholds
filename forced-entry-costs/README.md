# Forced-entry costs at a fixed optimal assignment under paired interval uncertainty

*A Lean-verified exact reduction and its consequences for linear programs.*

Paper: [`paper/forced_entry_costs.pdf`](paper/forced_entry_costs.pdf) (LaTeX source and BibTeX file in `paper/`),
by Filip Majchrzak (SAPIO MORPHEUS project).

Archived version: Zenodo, DOI [10.5281/zenodo.24511022](https://doi.org/10.5281/zenodo.24511022).

## The setting

The cost matrix `C(theta)` of an assignment problem depends on interval parameters `theta`, and one assignment `F`
is optimal in every scenario. For an entry `e` outside `F`, the *forcing cost* `h_e(theta)` is the extra cost of the
best assignment that uses `e`. The paper studies its smallest value over all scenarios, `eta_e` (a tolerance-type
quantity of sensitivity analysis), in a deliberately restricted model:

- (C1) `F` is the unique optimum in every scenario, with an explicit dual certificate;
- (C2) every parameter occurs in exactly two entries with coefficient `+1`, one of them in `F`;
- (C3) the uncertain entries form a matching;
- (C4) all costs are nonnegative.

## The statements

**Theorem 2 (exact adapter; machine-checked).** Every quadratic shortest-path instance on a directed acyclic graph
with nonnegative coefficients is turned, by an explicit construction without perturbation, into an assignment
instance of dimension `N = |V| + |A| + 4|J|` satisfying (C1)-(C4), such that in every scenario the forcing cost
equals a fixed constant plus the value of a linear shortest-path problem on the same graph, and `eta_e` equals
that constant plus the quadratic optimum.

**Consequences proved in the paper (not machine-checked).**

- Proposition 1: if the costs are nondecreasing in the parameters and no parameter is shared between an entry of `F`
  and an entry outside `F`, then `eta_e` is obtained from a single assignment problem. The sign condition is needed.
- Corollary 3: computing `eta_e` is NP-hard in the model (C1)-(C4), already for weights in `{1, 5}`.
- Corollary 4: for general instances of the model, `eta_e` cannot be approximated within a factor `2^poly(N)` unless
  P = NP.
- Proposition 9: the largest forcing cost over the scenarios is a linear program; for the explicit family below it
  has a representation with `4n^2` inequalities.

**Linear programs (known bounds, transported by short lemmas; not claimed as new).** For linear programs with a
fixed feasible region and an objective affine in the weights, and an explicit family of `N x N` instances,
`N = 8n^2 - n + 1`:

- Theorems 6 and 7: the exact size equals the extension complexity of the correlation polytope `COR(n)`, hence is at
  least `1.5^n` (Kaibel and Weltge), also for weights in `{1,...,5}`;
- Corollary 8: for interactions along the edges of a graph `G` the exact size is `xc(COR(G))`: at most
  `2^O(tw(G) + log n)`, with a matching lower bound in proper minor-closed classes (Aboulker, Fiorini, Huynh, Macchia
  and Seif), and `2^Omega(n / log n)`, in dimension `O(n)`, for the explicit bounded-degree graphs of Göös, Jain and
  Watson;
- Theorem 10: every fixed additive error still needs `2^Omega(n)` inequalities (corruption lemma of Braun, Fiorini,
  Pokutta and Steurer);
- Theorem 11: for weights in `[1, 5]` every fixed relative error is achieved with `n^O(1/eps^2)` inequalities
  (correlation rounding).

## What has been checked, and what has not

- **Lean 4 (Theorem 2 in full).** The directory [`lean/`](lean/) contains a Lean 4 project with Mathlib: the
  dimension, conditions (C1)-(C4) including uniqueness of the optimum among all doubly stochastic matrices, the
  formula for `h_e(theta)` in every scenario and the formula for `eta_e`. No `sorry`; only the three standard axioms;
  the Birkhoff-von Neumann theorem is taken from Mathlib. See [`lean/README.md`](lean/README.md) for the exact
  statements, for what is not proved, and for the clean-room record. The same project contains a formalisation of
  the classical covering inequality of Kaibel and Weltge.
- **Not machine-checked:** Propositions 1 and 9, Corollaries 3, 4 and 8, and everything on linear programs
  (Theorems 6, 7, 10, 11 and their lemmas). These have written proofs.
- **Independent implementations and computations.** The construction was implemented independently four times, once
  from a written description and three times from Section 2 of the paper, and checked in exact arithmetic on small
  and random instances; the other statements were checked on small cases. See [`verify/`](verify/). These
  computations are consistency checks, not proofs.
- **Internal review.** Separate AI agents of the same project re-derived the proofs, reviewed the text and checked
  the passages added during revision, each with its own code.

**Not done:** no external expert has reviewed the paper. The literature search was limited to open sources; the
full texts of three related works (Hladík, EJOR 336 (2027); Kasperski and Zieliński, EJOR 200 (2010); Fortin,
Zieliński, Dubois and Fargier, J. Sched. 13 (2010)) could not be read, so an overlap with the main claim cannot be
excluded. We make no priority claim beyond what the paper states, and we welcome corrections.

## Reproduce

Lean (requirements: `elan`, `git`, about 6 GB of disk):

```bash
cd lean
lake exe cache get
./scripts/check.sh
```

Scripts (requirements: Python 3 with `numpy` and `scipy`; `networkx` is optional): see
[`verify/README.md`](verify/README.md).

## Authorship and use of AI

This work was carried out with substantial assistance from AI systems working under the author's direction; the
SAPIO MORPHEUS project uses models from OpenAI and Anthropic. The construction, the theorems on linear programs,
their first proofs and three of the Lean modules were produced by an AI operator based on OpenAI models. The
independent reviews, the literature comparison, Propositions 1 and 9, Corollaries 3, 4 and 8, the manuscript and the
Lean formalisation of Theorem 2 were produced by AI agents based on Anthropic's Claude. The author selected the
problem and the direction, set the standards of rigour, made the decisions, and takes responsibility for the
content. See the last section of the paper.

## License

Code: Apache License 2.0. Paper: CC BY 4.0.
