# Palomar candidate status

- Published baseline: `b4c5b60f61766ea11cb7e72cc493181ac06f6c68` (unchanged on main).
- Preprint: https://doi.org/10.5281/zenodo.24523144
- Candidate: independent Challenge, matching Solution, four explicit fixed definitions, three compared theorems, metadata, pinned Lean and Mathlib, module-system port.
- The archived logs describe the baseline only. The first two CI runs successfully compiled Challenge and Solution and the needed proof modules. Comparator then rejected the configuration because definition_names is reserved for deliberate definition holes. This correction leaves both Lean sources unchanged and removes the four fixed definitions from definition_names; the three theorem targets and permitted axioms are unchanged. Comparator acceptance still requires a fresh successful run. See https://github.com/kosza123/flow-certificate-thresholds/actions/runs/45613327417.
- The branch contains an isolated copy of the full Kenyon proof, not the other unrelated papers on main.
- The configured GitHub Actions run uses only a standard public Linux runner, with no paid services or artifact uploads. If the run does not start, launch only after confirming there are no additional charges.
- No submission to or registration with Palomar has been made.
- Do not claim external verification or priority until independently established.
