import Mathlib

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ : L → R)

variable [LinearWeights R L M]

private theorem aux [h : Nontrivial (LieModule.shiftedGenWeightSpace R L M χ)] : genWeightSpace M χ ≠ ⊥ := (LieSubmodule.nontrivial_iff_ne_bot _ _ _).mp h


theorem toEnd_eq (x : L) :
    toEnd R L (LieModule.shiftedGenWeightSpace R L M χ) x =
    (shift R L M χ).conj (toEnd R L (genWeightSpace M χ) x - χ x • LinearMap.id) := by
  tauto

