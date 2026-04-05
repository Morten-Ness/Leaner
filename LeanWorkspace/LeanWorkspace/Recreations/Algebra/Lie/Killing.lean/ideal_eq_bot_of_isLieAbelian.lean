import Mathlib

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

variable [IsKilling R L]

set_option backward.isDefEq.respectTransparency false in
theorem ideal_eq_bot_of_isLieAbelian
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]
    (I : LieIdeal R L) [IsLieAbelian I] : I = ⊥ := by
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

