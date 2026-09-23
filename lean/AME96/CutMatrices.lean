import AME96.CutData

namespace AME96
open Matrix
open scoped BigOperators
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem leftInverse_entries : ∀ (k : Fin 126) (i j : Fin 4),
    (cutLeftInverse k * cBlock (cutSelected k) (cutOutside k)) i j =
      (1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) i j := by
  change ∀ (k : Fin 126) (i j : Fin 4),
    (∑ u : Fin 5, cutLeftInverse k i u * C (cutOutside k u) (cutSelected k j) : ZMod 3) =
      if i = j then 1 else 0
  decide +kernel

private theorem compatible_entries : ∀ (k : Fin 126) (i j : Fin 4),
    (cutLeftInverse k * tBlock (cutSelected k) (cutOutside k)) i j =
      (-cutCompatible k) i j := by
  change ∀ (k : Fin 126) (i j : Fin 4),
    (∑ u : Fin 5, cutLeftInverse k i u * B (cutSelected k j) (cutOutside k u) : ZMod 3) =
      -(cutCompatible k i j)
  decide +kernel

theorem cutLeftInverse_valid (k : Fin 126) :
    cutLeftInverse k * cBlock (cutSelected k) (cutOutside k) = 1 :=
  funext fun i => funext fun j => leftInverse_entries k i j

theorem cutCompatible_valid (k : Fin 126) :
    cutLeftInverse k * tBlock (cutSelected k) (cutOutside k) = -cutCompatible k :=
  funext fun i => funext fun j => compatible_entries k i j

end AME96
