# Changes

## Version 2.1.0 (26 November 2026)

Zenodo: [10.5281/zenodo.24562023](https://doi.org/10.5281/zenodo.24562023).

* **New in the paper: Remark "Exact arithmetic in resistor networks"** (after the corollary on currents). In a
  connected network of `m` unit resistors fed by a unit current, every node potential (measured from a terminal)
  and every branch current is a rational number whose denominator divides `tau(G)`; by Theorem 1 it has at most
  `ceil((m/2) log2(27/8))` binary digits, about `0.8774 m`. The proof is Cramer's rule for the reduced Laplacian.
  Not formalised.
* **Paper: independent reproduction.** A paragraph on the reproduction by Carles Marín (see below) and a revised
  "What has not been done".
* **Paper: Question (1)** now cites the exact values of `T(m)` and the extremal multigraphs for `m <= 22` computed
  by Marín (doi:10.5281/zenodo.24561280) and the structural results of the author's preliminary note
  (doi:10.5281/zenodo.24562316).
* **Paper: new subsection "Context and possible applications"**, which states the three consequences in
  neighbouring areas and says explicitly that no practical advantage in the design of real networks has been shown.
* **Lean: `Kenyon.numTrees_K4`** in `lean-kenyon/Kenyon/Examples.lean`: the complete graph on four vertices has
  16 spanning trees (a third example next to `numTrees_loop` and `numTrees_digon`), as suggested by Carles Marín.
  `scripts/PrintAxioms.lean` reports it, so `check.sh` now prints 40 axiom reports. No other Lean file changed. A
  new clean-room run, by an AI session that did not write the change (40 axiom reports, kernel replay of 29
  modules, three negative controls, SHA-256 of all 39 files), is recorded in
  `lean-kenyon/VERIFICATION_CLEANROOM_2.1.txt` with raw outputs in `lean-kenyon/logs_2.1/`; the run of version
  2.0.0 is kept in `lean-kenyon/VERIFICATION_CLEANROOM.txt` and `lean-kenyon/logs/`.
* Unchanged: the statements and proofs of the paper, `verify/`, and the Lean package of version 1 in `lean/`.

## After version 2.0.0 (GitHub only; not a new archived version)

* **26 November 2026: independent reproduction recorded in the README.** Carles Marín rebuilt `lean-kenyon/` at
  commit `b4c5b60` on Windows 11 with the unmodified `scripts/check.sh` (39 axiom reports, kernel replay of 29
  modules, the 39 recorded SHA-256 sums match), checked the axioms and the faithfulness of the definitions and of
  the two final statements, and tested the definition of `tau` with his own Lean-verified decider. Stated with his
  permission; he was assisted by an AI system (Claude). The paper, the Lean sources and the recorded verification
  are unchanged. His suggestions for a later version: an example such as K4 = 16 in `Kenyon/Examples.lean`, and a
  non-release-candidate Lean toolchain.

## Version 2.0.0 (25 November 2026)

Zenodo: [10.5281/zenodo.24523144](https://doi.org/10.5281/zenodo.24523144).

* **New: complete Lean 4 formalisation of the bound and of its sharpness** (directory
  `lean-kenyon/`). `Kenyon.kenyon_bound`: every finite multigraph with `m ≥ 1` edges satisfies
  `τ² · 8^m < 27^m`. `Kenyon.kenyon_sharp`: for every `0 < c < 27/8` there is a multigraph with
  `c^m < τ²`. These are Theorem 1 and Corollary 3 of the paper. Recorded clean-room run and raw
  outputs: `lean-kenyon/VERIFICATION_CLEANROOM.txt`, `lean-kenyon/logs/`.
* **New: Section 10 of the paper**, a second proof of Theorem 1 and a direct proof of the lower
  bound in Corollary 3. This is the route that Lean checks; it is also listed, with the names of
  the Lean theorems, in `lean-kenyon/PROOF_ROUTE.md`.
* The paper's title line, abstract, the paragraph on the status of verification, Appendix A and
  the statement on the use of AI are updated accordingly. Sections 2 to 9 of the paper are
  unchanged.
* Unchanged: the statements of the paper, the first proof (Sections 2 to 7), the literature
  section with its limits, `verify/`, and the Lean package of version 1 in `lean/`.
* Not formalised: Proposition 2 in its generality, Corollaries 4 and 5, the equality statement,
  and the lemmas of Sections 3 to 5 as stated there. See the paper and `lean-kenyon/README.md`.

## Version 1.0.0 (24 November 2026)

Zenodo: [10.5281/zenodo.24504455](https://doi.org/10.5281/zenodo.24504455).

The paper, the verification scripts and the Lean package `TreeEntropy` for the key inequality
(`lean/`). In this version the theorem as a whole was not machine-checked. The paper of version 1
is kept in `paper/v1.0.0/`.
