import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable {N : LieSubmodule R L M} {x : L}

theorem toEnd_restrict_eq_toEnd (h := N.toEnd_comp_subtype_mem x) :
    (toEnd R L M x).restrict h = toEnd R L N x := by
  rfl

