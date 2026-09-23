# FC-compatible AME(9,6) proof

This project imports Formal Conjectures at commit `2a46c7bd74505b85f4967475bb733ded0ef8d348`, using Lean `v4.33.1` and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

The exact answer-filled target is in [`AME96/FormalTarget.lean`](AME96/FormalTarget.lean):

```lean
theorem AME96.ame_9_6_answer_true :
    answer(True) ↔ OpenQuantumProblem35.ExistsAME 9 6
```

It follows from the explicit existence theorem in [`AME96/Existence.lean`](AME96/Existence.lean). The open FC declaration is never used as a premise.

## Rebuild

```sh
lake update
lake exe cache get
python3 scripts/build_audit.py
```

The audit script runs `lake --wfail build AME96 AME96.Audit`, saves the build log and source hashes in `evidence/`, and requires the final existence and answer-filled target to have only the usual `propext`, `Classical.choice`, `Quot.sound` dependencies. A fresh machine may need substantial time and disk space to fetch and compile mathlib and Formal Conjectures.

The recorded local run passed; see [`evidence/build_results.json`](evidence/build_results.json) and [`evidence/build.log`](evidence/build.log).

## Proof path

`Data`, `State`, `Polynomial`, `Partition`, `MixedPhase` and `CharacterSum` define the witness and derive the phase identity. `Certificate`, `CutData`, `FastChecks`, `CutMatrices` and `CutCoverage` verify a finite certificate for all 126 cuts. `AllCuts`, `Reduction` and `Existence` turn those checks into the FC partial-trace condition and existence theorem. `FormalTarget` supplies the explicit `answer(True)` statement. `Audit` prints the main axiom dependencies.

The certificate checks 126 × 80 nonzero binary differences and uses a left-inverse argument to cover all 826,560 nonzero difference types. Python scripts under `scripts/` generate the finite data; Lean checks their output with `decide +kernel`.

The source manuscript under `evidence/` predates the Lean proof and is retained for attribution. See [Sources and provenance](../README.md#sources-and-provenance).
