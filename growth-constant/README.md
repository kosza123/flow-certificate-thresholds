# Two-port substitution and the growth of the smallest current in planar networks

Second note of the SAPIO MORPHEUS project by Filip Majchrzak. It lives in this repository because its Lean package
imports one module of the first development (`PlanarCore.Fekete`).

- Paper: [`paper/twoport_growth.pdf`](paper/twoport_growth.pdf), with LaTeX source.
- Zenodo: DOI 10.5281/zenodo.24497700 (reserved for this note).

## The result in one paragraph

In a planar network of `q` unit resistors fed through two terminals on a common face, let `Λ_q` be the largest value
of `1/|I|` over nonzero branch currents. Equivalently, `Λ_q` is the largest ratio (longest side)/(smallest square) in
a rectangle tiled by at most `q` squares. The limit `c = lim Λ_q^(1/q)` exists. Every network `X` with a marked edge
has a 2×2 matrix `N_X` of determinant 1 with `c ≥ ρ(N_X)^(1/(q−1))`, and `c` is the supremum of these numbers. An
explicit 23-edge network gives **`c ≥ 1.7194145…`**, above the golden ratio of the Fibonacci tiling. The best upper
bound known to us is 1.8393 (Stoimenow). We do not claim priority; see the paper for what is classical.

## Contents

| Path | Content |
|---|---|
| `paper/` | the note (PDF and LaTeX) |
| `../twoport/` | Lean 4 package `TwoPort`: substitution lemma, Möbius form, composition, iteration, growth bound, the example `H7` |
| `verify/verify_gadgets.py` | exact-arithmetic check of the two explicit gadgets (Python 3 with networkx) |
| `verify/gadgets.json` | edge lists and matrices of the gadgets found by the search (orders 21 to 29) |
| `VERIFICATION_CLEANROOM.txt` | record of a build from an empty directory with a freshly downloaded Mathlib |

## Reproduce

Lean (needs [elan](https://github.com/leanprover/elan), git and network access):

```bash
cd twoport
lake exe cache get
./scripts/check.sh
```

Expected last line: `OK: build, 21 axiom reports, kernel replay of 7 modules`.

Exact check of the gadgets:

```bash
python3 growth-constant/verify/verify_gadgets.py
```

Expected last line: `ALL CHECKS PASSED`.

## What is and is not machine-checked

- **Checked in Lean:** the substitution lemma, the Möbius form with `det = Q²`, composition as a matrix product,
  the iteration formula `|I_k| = 1/y_k`, the growth bound, the row-sum inequality, and the example `H7`.
- **Explicit hypotheses in Lean:** planarity of the iterated networks with terminals on a common face, the
  hypotheses of the Fekete step, positivity of the matrix entries, and the existence of the open-circuit potentials.
- **Not formalised:** the transposition theorem, the "≤" direction of the characterisation, the interpretation of
  the matrix entries as spanning-tree counts, and the numerical results other than `H7`. The 23-edge gadget is
  checked by exact computation, not by Lean.

## Notes on the verification record

`VERIFICATION_CLEANROOM.txt` is the unedited record of the clean-room run. After that run:
- `verify/verify_gadgets.py` was changed in one line so that it can be started from any directory; its output is
  unchanged;
- the text of the paper was revised after a second review;
- the Lean sources were not changed.

## AI assistance

This work was carried out with substantial assistance from AI systems under the author's direction; see the section
"Author contributions and use of AI" in the paper. The author is responsible for the content.

## License

Lean code and scripts: Apache License 2.0. Paper: CC BY 4.0.
