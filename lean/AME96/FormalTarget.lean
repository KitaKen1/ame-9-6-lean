import AME96.Existence

/-!
The exact proposition appearing on the right of the pinned Formal Conjectures
`OpenQuantumProblem35.ame_9_6_open` declaration is `ExistsAME 9 6`.
Filling its answer with `True` gives the following target, proved from the
explicit state without using the open declaration.
-/

namespace AME96
open OpenQuantumProblem35

theorem ame_9_6_answer_true : answer(True) ↔ ExistsAME 9 6 := by
  constructor
  · intro _
    exact exists_ame_9_6
  · intro _
    trivial

end AME96
