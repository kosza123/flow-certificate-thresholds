# Verification record

## 1. Clean-room run of this package (24 November 2026, package snapshot f932b49)

The full record, with exact outputs and the sha256 of every checked file, is in
[`VERIFICATION_CLEANROOM.txt`](VERIFICATION_CLEANROOM.txt).

**Procedure.**
- The package was copied, without `.lake`, into a new empty directory.
- Mathlib was cloned afresh, and an empty `MATHLIB_CACHE_DIR` forced a fresh download of the cache.
- `./scripts/check.sh` was run unchanged.

**Results.**
- Overall: PASS, exit code 0, `ALL CHECKS PASSED`, 185 s wall time. An earlier run on a snapshot with the same
  code and older comments also passed (275 s).
- Mathlib cache: 9139 of 9139 files downloaded.
- Build: `Build completed successfully (18329 jobs).`
- Search for `sorry`, `admit` and `axiom`: none found.
- `#print axioms`: 15 of the 16 listed declarations depend on `[propext, Classical.choice, Quot.sound]`.
  `RotCert.dual_connected` depends only on `[propext, Quot.sound]`. The script prints these lines and does not
  check them automatically; they were inspected by hand.
- `leanchecker`: all 12 modules replay without error.

**Versions.**
- Lean 4.37.0-rc1 (commit 0b77e129).
- Lake 5.0.0.
- Mathlib `53dad9ed98be8416b6ca1111e55a03de4303231f`.

**Note.** Since release 1.0.0, `scripts/check.sh` also fails automatically on unexpected axioms
(`scripts/check_axioms.sh`); see the later notes in `VERIFICATION_CLEANROOM.txt`.

**Limitation.** The run used the same machine as the development and reused the locally installed Lean toolchain
binary, which was not downloaded again.

**Code identity.** The 13 `.lean` files are identical, apart from comments, to the development snapshot that was
checked earlier. In this release only references to unpublished working notes were removed from the comments.
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are byte-identical to that snapshot.

## 2. Separate numerical cross-check (not part of the proof; written by the same AI agents)

The threshold was recomputed by linear programming (HiGHS) on the explicit networks. Each result was compared with
`|I_e|/(1+|I_e|)` computed in exact rational arithmetic.

- Coverage: all 1556 admissible triples `(s, t, e)` on eight planar multigraphs: a triangle with a pendant edge,
  `K4` with a doubled edge, fans with path lengths 2 to 5, the octahedron and the cube.
- Largest deviation: 1.1e-15. None of the tested graphs has loops.
- Optima: −1 for network A and 0 for network B in every case.

See paper, Section 6.
