# Lean4Web edition

[`AME96Lean4Web.lean`](AME96Lean4Web.lean) is the single-file Mathlib-only edition of the AME(9,6) proof. It uses Lean/mathlib `v4.35.0-rc2` and proves both the existence statement and the explicit `answer(True) ↔ ExistsAME 9 6` target.

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fame-9-6-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FAME96Lean4Web.lean)
and select Lean/mathlib `v4.35.0-rc2`. The top of the file checks
`Lean.versionString`; the bottom prints the two theorem types and their axiom
dependencies. Full checking may take time because the file contains all 126
finite cut checks.

Local verification:

```sh
lake update
lake exe cache get
lake --wfail build AME96Lean4Web
```

The local build passed with Lean `4.35.0-rc2`; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound` for both final theorems.

To regenerate the file after changing the FC-compatible proof, first run `lake update` in `../lean`, then run `python3 generate_source.py` here. The generator extracts the needed FC definitions from the pinned checkout, removes FC-specific metadata attributes, and concatenates the proof modules. For mathlib `v4.35.0-rc2`, it changes two calls to the renamed subtype equivalence from `Equiv.setCongr` to `Set.equivOfEq`; the proof statement and argument are unchanged. This standalone edition has no runtime Formal Conjectures import; the FC-compatible edition in `../lean/` checks against the actual library target.
