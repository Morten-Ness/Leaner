import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem isNonZero_iff_ne_zero [Nontrivial (LieModule.genWeightSpace M (0 : L → R))] {χ : LieModule.Weight R L M} :
    χ.IsNonZero ↔ χ ≠ 0 := LieModule.Weight.isZero_iff_eq_zero.not

noncomputable instance : DecidablePred (IsNonZero (R := R) (L := L) (M := M)) := Classical.decPred _

