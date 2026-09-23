# AME(9,6) priority audit — 23 September 2026

## Conclusion and scope

No prior public solution of the unrestricted **existence** question for an
AME(9,6) pure state was identified in the sources below. The construction in
this repository is therefore a **plausibly new solution to this parameter
case**, not an established claim of first publication or an exhaustive
priority determination. A proof that no earlier result exists is not possible
from an indexed-literature search; unindexed preprints, private work,
alternative terminology, and new reports after a source's cutoff remain
possible.

The mathematical proof and the priority claim are separate. The Lean package
proves `OpenQuantumProblem35.ExistsAME 9 6` against a pinned Formal
Conjectures definition; its successful build and axiom audit are recorded in
[`build_results.json`](build_results.json). They do not certify novelty.

## Dated source evidence

| Source | What it establishes | Limit |
| --- | --- | --- |
| [Rajchel-Mieldzioć et al., 2026 survey](https://arxiv.org/abs/2508.04777), revised 25 June 2026 | Figure 7 compiles existence status by party number and local dimension; blank cells denote open cases. This is the baseline used by the more recent parameter audits. | A survey snapshot, not a continuously updated registry. |
| [QIQCOP Zoo, “Unclassified existence parameters for homogeneous AME states”](https://qiqc-op.com/problem/op_439ae5e7e9b3b043/), last edited 9 September 2026 | Explicitly lists `(9,6)` among unrestricted unresolved AME existence pairs; it removes other newly solved cases such as `(7,6)` and `(12,5)`. | A dated research index, not a proof that nothing was known elsewhere or after 9 September. |
| [Hontarenko–Życzkowski, arXiv:2609.11796v1](https://arxiv.org/abs/2609.11796v1), submitted 10 September 2026 | Its Figure 1 existence map records the `(d,N)=(6,9)` cell as unsettled. Supplemental Section S15 says its literature comparison stops at 5 September 2026. Its new family has odd prime-power local dimension `q`, so it does not construct a state at local dimension 6. | The paper cannot exclude a later report, and its map is a compilation of cited literature. |
| [Bevins–Bidav, arXiv:2608.05781v2](https://arxiv.org/abs/2608.05781v2), revised 10 August 2026 | Its five new AME pairs are `(12,5)`, `(18,11)`, `(18,13)`, `(17,11)`, and `(17,13)`; none is `(9,6)`. | This only rules out that particular recent construction as the same-parameter result. |
| [Formal Conjectures `OpenQuantumProblems/35.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OpenQuantumProblems/35.lean) and [OQP Problem 35](https://oqp.iqoqi.oeaw.ac.at/existence-of-absolutely-maximally-entangled-pure-states) | The FC file still displays `ame_9_6_open` as `answer(sorry) ↔ ExistsAME 9 6`; OQP explains the unrestricted AME existence question. | Repository labels can lag the research literature. The overall OQP classification remains open even if one parameter is solved. |

Exact-parameter public searches checked `AME(9,6)`, `AME(9, 6)`,
`ExistsAME 9 6`, nine six-level parties, nine quhexes, and the equivalent
four-uniform / `((9,1,5))_6` quantum-code terminology. No prior public
construction or Lean proof was found in those searches. Search engines have
weak coverage for mathematical notation, so a negative search result is
supporting evidence only. The 22 September issue/PR audit recorded in
[`AME_9_6_complete_proof_20260922.md`](AME_9_6_complete_proof_20260922.md)
found neighboring FC cases but no same-parameter solution; that check was
bounded to public, discoverable items at the time.

## Claims suitable for a public manuscript

“We give an explicit construction and Lean proof of an AME(9,6) state, a
parameter listed as unresolved in sources dated September 2026.” The stronger
claim “the first solution” should wait for an updated literature and code
search at submission time and independent expert review. Neither the
existence of AME(4,6) nor constructions in odd prime-power local dimensions
automatically solve the nine-party, six-level case.
