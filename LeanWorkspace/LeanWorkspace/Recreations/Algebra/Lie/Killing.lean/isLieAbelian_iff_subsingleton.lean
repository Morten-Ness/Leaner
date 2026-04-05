import Mathlib

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

variable [IsKilling R L]

theorem isLieAbelian_iff_subsingleton
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    IsLieAbelian L ↔ Subsingleton L := by
  constructor
  · intro h
    rw [isLieAbelian_iff_center_eq_top R] at h
    have hc : (⊤ : LieIdeal R L) = ⊥ := by rw [← center_eq_bot R L, h]
    exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_top_eq_bot hc)
  · exact fun _ => inferInstance

