<p align="center"><img src="assets/logo_wordmark.png" alt="SAPIO MORPHEUS" width="520"></p>

# Machine-checked flow-certificate thresholds for planar graphs

Lean 4 formalisation and paper: *Machine-Checked Flow-Certificate Thresholds for Planar Graphs Using
Rotation-System Certificates* by Filip Majchrzak (SAPIO MORPHEUS project).

- Paper: [`paper/flow_certificate_thresholds.pdf`](paper/flow_certificate_thresholds.pdf), with its LaTeX source in `paper/`.
- Source code: <https://github.com/kosza123/flow-certificate-thresholds>.
- Archived on Zenodo: version 1.1, DOI [10.5281/zenodo.24496271](https://doi.org/10.5281/zenodo.24496271); all
  versions, DOI [10.5281/zenodo.24488175](https://doi.org/10.5281/zenodo.24488175); version 1.0.0, DOI
  [10.5281/zenodo.24488176](https://doi.org/10.5281/zenodo.24488176).
- Version 1.1 adds the literature on squared rectangles to the paper (Section 7 and Appendix A). Version 1.0.1 added
  an automatic axiom check to `scripts/check.sh`. The Lean sources are unchanged since 1.0.0.

## Second note: growth of the smallest current

The directory [`growth-constant/`](growth-constant/) contains a second note, *Two-Port Substitution and the Growth of
the Smallest Current in Planar Networks*, and [`twoport/`](twoport/) contains its Lean package. It shows that the
growth constant of the ratio (longest side)/(smallest square) of squared rectangles is at least 1.7194145. See
[`growth-constant/README.md`](growth-constant/README.md).

## Third note: spanning trees per edge

The directory [`spanning-trees-per-edge/`](spanning-trees-per-edge/) contains a third paper, *Spanning Trees per
Edge: A Sharp Bound and a Question of Kenyon*, with its verification scripts and a Lean package for the key
inequality. It proves that every multigraph with `m >= 1` edges has fewer than `(27/8)^(m/2)` spanning trees, with
the base `sqrt(27/8) = 1.8371...` best possible. Archived on Zenodo, DOI
[10.5281/zenodo.24504455](https://doi.org/10.5281/zenodo.24504455). The theorem as a whole is not machine-checked
and has not yet been reviewed by an external expert; see
[`spanning-trees-per-edge/README.md`](spanning-trees-per-edge/README.md).

## The statement

Let `G` be a connected planar multigraph with unit resistances. Pick terminals `s`, `t` and an edge `e` that
carries a nonzero current `I_e` when one unit of current is fed in at `s` and taken out at `t`.

From `G` and its plane dual we build two capacitated min-cost circulation networks, `A` and `B`, on one shared
topology. Their observed arcs are indexed by the edges of `G`.

**Theorem 1.** Consider the smallest additive tolerance `ε` such that `A` and `B` have feasible circulations
that agree on every observed arc, each within `ε` of its own optimum. That smallest `ε` is

```
|I_e| / (1 + |I_e|)  =  |N| / (D + |N|),
```

where `D = det(A Aᵀ) > 0` is the reduced Laplacian determinant and `N` is an integer Cramer numerator with
`I_e = N / D`.

The dual must be oriented consistently: every dual edge crosses its primal edge in the same direction. With an
inconsistent orientation the statement fails (paper, Remark 1). In Lean the orientation is fixed by the
certificate.

By the classical matrix-tree theorem, `D` is the number of spanning trees and `|N|` is a signed spanning-tree
count. That identification is classical and **not** formalised here.

## What the Lean code proves

`PlanarCore.theorem1_certified` (file `PlanarCore/Final.lean`) has three hypotheses:

1. `G` is connected;
2. `C : RotCert G f` is a genus-0 rotation-system certificate for `G`;
3. `I_e ≠ 0`.

From these it derives:

- `D > 0`;
- `I_e = N / D` with `N ∈ ℤ`;
- `IsLeast {ε | AdmissibleTransfer (netA …) (netB …) ε} (|N| / (D + |N|))`.

The two circulation networks are built explicitly, and the following are all proved, not assumed:

- the dual graph is computed from the certificate;
- `A Bᵀ = 0`;
- the dual is connected;
- `ker B = row A`;
- `0 ≤ I ≤ 1` after reorientation;
- the invertibility of `A Aᵀ`.

**Cited, not formalised.** A connected multigraph is planar if and only if it has a genus-0 rotation system.
This is the Heffter–Edmonds–Ringel rotation principle combined with Euler's formula. Inside Lean, "planar"
means "has a `RotCert`".

**Not formalised.** The following are not formalised:

- the matrix-tree identification of `D` and `N`;
- that the reoriented dual equals the dual of a certificate for the reoriented graph (immediate, argued in the
  paper, Section 5.3);
- the minimum over all `(s, t, e)`.

The auxiliary module `PlanarCore/Fekete.lean` formalises only an abstract Fekete-type step, with its
graph-theoretic inputs taken as hypotheses (paper, Appendix A).

## Reproduce

Requirements: [elan](https://github.com/leanprover/elan) (the Lean toolchain manager), git, and network access
to GitHub and the Mathlib cache.

```bash
git clone https://github.com/kosza123/flow-certificate-thresholds.git
cd flow-certificate-thresholds
./scripts/check.sh
```

The script runs five steps:

1. it fetches the prebuilt Mathlib cache with `lake exe cache get`;
2. it builds the library with `lake build`;
3. it checks that the sources contain no `sorry`, `admit` or `axiom`;
4. it prints the axioms of the main theorems (`scripts/PrintAxioms.lean`) and fails, via `scripts/check_axioms.sh`,
   if any report is missing or any axiom other than `propext`, `Classical.choice` or `Quot.sound` appears;
5. it replays every module in the kernel checker `leanchecker`.

Pinned versions:

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.37.0-rc1` (`lean-toolchain`) |
| Mathlib | commit `53dad9ed98be8416b6ca1111e55a03de4303231f` (`lakefile.toml`, `lake-manifest.json`) |

Expected results: the build succeeds, no forbidden tokens are found, and every listed theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`. The kernel replay passes for all 12 modules. See
[`VERIFICATION.md`](VERIFICATION.md) for the recorded outputs.

## Files

| File | Content |
|---|---|
| `PlanarCore/Graph.lean` | multigraph model, incidence matrices, currents, invertibility of `A Aᵀ`, `0 ≤ I ≤ 1` |
| `PlanarCore/Threshold.lean`, `Projection.lean`, `Assembly.lean` | threshold of two linear gaps; projection algebra |
| `PlanarCore/Network.lean` | the explicit circulation networks `netA`, `netB`; projections, costs, optima; `theorem1_networks` |
| `PlanarCore/Certificate.lean` | `RotCert`; dual, `A Bᵀ = 0`, dual connectivity, `ker B = row A` |
| `PlanarCore/Kirchhoff.lean` | `D > 0`, `I_e = N/D` (Cramer) |
| `PlanarCore/Final.lean` | `theorem1_certified` and a decided example (a triangle with a pendant edge) |
| `PlanarCore/Theorem1.lean`, `Sanity.lean`, `Necessity.lean` | intermediate integration, a non-vacuity check, and a counterexample showing `0 ≤ I ≤ 1` is needed |
| `PlanarCore/Fekete.lean` | auxiliary: abstract Fekete step and inequalities (paper, Appendix A) |
| `crosscheck/lp_crosscheck.py` | optional independent numerical check by linear programming (Python with networkx, sympy and scipy); not part of the proof |
| `VERIFICATION.md`, `VERIFICATION_CLEANROOM.txt` | recorded outputs of the clean-room run |

## Claims and priority

This work makes no claim to solve a known open problem.

- **Classical:** Kirchhoff's current formula, the matrix-tree theorem, planar duality, the rotation principle
  and Fekete's lemma.
- **Prior work:** Bu and Pan give a linear-algebraic planarity criterion through spanning-tree numbers and
  concatenated incidence matrices (SIAM J. Discrete Math. 39 (2025), doi:10.1137/24M1660395). For terminals on a
  common face, edge currents are the sides of a squared rectangle (Brooks, Smith, Stone and Tutte, 1940). The size of
  such tilings is bounded by Conway (1964), Kenyon (1996), Fomin (arXiv:2103.10523; base 1.8637) and Keleti, Lacina,
  Liu, Liu and Tuirán Rangel (2023). Chan, Kontorovich and Pak
  study inverse problems for effective resistance and spanning-tree counts.
- **Possibly new:** the two-network threshold statement as packaged here, and this formal development. Our
  literature search was limited and is described in the paper. We claim no priority.

## AI assistance

This project was carried out with substantial assistance from AI systems working under the author's direction.
The project uses models from OpenAI and Anthropic.

- The mathematical write-up behind the paper was drafted by one AI agent of the project.
- The Lean formalisation, the literature comparison and the manuscript were produced by AI agents based on
  Anthropic's Claude (Claude Code).
- Every formal claim is checked by the Lean kernel.
- The author selected the problem, directed the work, made the publication decisions and is responsible for the
  content.

## License

- Lean code and scripts: Apache License 2.0 (`LICENSE`).
- Paper (text and figures): Creative Commons Attribution 4.0 International (CC BY 4.0).

## Citation

See [`CITATION.cff`](CITATION.cff).
