# A Lean proof of an AME(9,6) state

This repository gives an explicit **absolutely maximally entangled state of nine
six-level parties** and a Lean proof of its existence. It addresses the
`AME(9,6)` instance of [Open Quantum Problem 35](https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states)
as formalized in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OpenQuantumProblems/35.lean).
For every choice of four parties, the state's reduced density matrix is
`I / 6^4`.

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fame-9-6-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FAME96Lean4Web.lean)
and select Lean/mathlib `v4.35.0-rc2`. This single-file edition includes the
final theorem and `#print axioms` checks. Full checking may take time because
it verifies all 126 four-party cuts.

The proof settles this **one existence instance**. The classification of all
pairs `(n,d)` in Open Quantum Problem 35 remains open.

## Formal Conjectures target

The `lean/` project imports Formal Conjectures at commit
`2a46c7bd74505b85f4967475bb733ded0ef8d348` and proves:

```lean
theorem AME96.exists_ame_9_6 :
    OpenQuantumProblem35.ExistsAME 9 6

theorem AME96.ame_9_6_answer_true :
    answer(True) ↔ OpenQuantumProblem35.ExistsAME 9 6
```

The second theorem fills the answer with `True`. It is a new theorem using
the actual Formal Conjectures definitions and `answer` elaborator. The
repository does not edit the upstream `ame_9_6_open` declaration, whose
`answer(sorry)` placeholder remains in the pinned source; that unfinished
declaration is never used as a premise. The proof establishes its intended
existence proposition directly.

## Mathematical explanation

Write each local basis label as `3x+y`, where `x ∈ {0,1}` and
`y ∈ {0,1,2}`. With `ω = exp(2πi/3)`, the witness is the uniform-magnitude
phase state

$$
|\Psi\rangle
=6^{-9/2}\!\sum_{x\in\{0,1\}^{9}}\sum_{y\in\mathbb F_3^{9}}
(-1)^{q_G(x)}
\omega^{q_C(y)+x^{\mathsf T}By+q_H(x)}
|3x+y\rangle .
$$

Here `3x+y` is taken componentwise, the binary quadratic phase is reduced
modulo 2, and the other phases are reduced modulo 3.

The four explicit matrices `G, B, H, C` are in
[`lean/AME96/Data.lean`](lean/AME96/Data.lean); their mathematical form and
the meaning of the mixed binary–ternary term are in the
[source proof](lean/evidence/AME_9_6_complete_proof_20260922.md).

For a set `S` of four parties, trace out its five-party complement `O`.
For an off-diagonal entry, the environment sum is, up to an overall phase of
modulus one, the product of one ternary and one binary character sum per site:

$$
6^{-9}\prod_{i\in O}
  (1+\omega^{\alpha_i}+\omega^{2\alpha_i})
\prod_{i\in O}
  (1+(-1)^{r_i}\omega^{\beta_i}).
$$

A ternary factor vanishes when `αᵢ ≠ 0`; a binary factor vanishes when
`rᵢ = 1` and `βᵢ = 0`. The finite certificate checks that one of these
cancellations occurs for every nonzero internal difference on every one of the
`binom(9,4) = 126` cuts. Lean proves that the certificate covers all
off-diagonal entries, then derives that each diagonal entry is `6^(-4)`.
The same equal-magnitude amplitudes give norm one. Thus each four-party
reduction is `I / 1296`, which is exactly the imported `IsAME` condition.

The matrices were found by search.
Search output is not trusted by the Lean proof: the finite data are checked
with `decide +kernel`, and the character-sum and partial-trace arguments
are proved in Lean.

## Files

| Directory | Lean version | Purpose |
| --- | --- | --- |
| [`lean/`](lean/) | `v4.33.1` | Imports pinned Formal Conjectures and proves the exact `ExistsAME 9 6` and `answer(True)` targets. |
| [`lean4web/`](lean4web/) | `v4.35.0-rc2` | Generated single-file, Mathlib-only edition for Lean4Web. |

The standalone edition reproduces the FC definitions needed for the proof
without FC metadata attributes or an FC runtime import. Its local
`answer(True)` elaborates to `True`, as the default FC answer does at this
explicit value. The `lean/` project is the authoritative check against the
imported FC target. Module details and generation instructions are in the
[`lean/` README](lean/README.md) and
[`lean4web/` README](lean4web/README.md).

## Verification

Formal Conjectures edition:

```bash
cd lean
lake update
lake exe cache get
python3 scripts/build_audit.py
```

Standalone Lean4Web edition, checked locally:

```bash
cd lean4web
lake update
lake exe cache get
lake --wfail build AME96Lean4Web
```

Both local builds passed. The FC audit verifies all 126 cuts and records the
build, source hashes and axiom closure in
[`lean/evidence/build_results.json`](lean/evidence/build_results.json).
The two final theorems depend only on the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; they do not depend on
`sorryAx`, `native_decide`, or a custom axiom.

## Status boundary

**Solved:** An explicit normalized pure state satisfies
`OpenQuantumProblem35.ExistsAME 9 6`, including every four-party reduction.
The answer-filled FC statement is proved as `answer(True) ↔ ExistsAME 9 6`.

**Open:** The general classification `oqp_35` of all `(n,d)` is not
settled here. This proof makes no claim about other party counts, optimal
support, or local-unitary classification.

## Sources and provenance

- [Open Quantum Problem 35](https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states)
  and its [Formal Conjectures definition](https://github.com/google-deepmind/formal-conjectures/blob/2a46c7bd74505b85f4967475bb733ded0ef8d348/FormalConjectures/OpenQuantumProblems/35.lean).
- The character-sum, conjugation and norm proofs in `AME96/Phase.lean`,
  `character_sum` in `AME96/CharacterSum.lean`, and the initial quadratic
  identities in `AME96/Polynomial.lean` adapt
  [`GraphCharacter.lean` from KitaKen1/ame-11-10-lean](https://github.com/KitaKen1/ame-11-10-lean/blob/6b7d009a43970587a3386b690221bec4339ce271/lean/GraphCharacter.lean)
  at commit `6b7d009a43970587a3386b690221bec4339ce271` (Apache-2.0).
  The binary–ternary specialization and mixed-cancellation interface are for this construction.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code using Claude Opus 5.5.
