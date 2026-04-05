import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem isNilpotent_toEnd_sub_algebraMap [IsNoetherian R M] (χ : L → R) (x : L) :
    _root_.IsNilpotent <| toEnd R L (LieModule.genWeightSpace M χ) x - algebraMap R _ (χ x) := by
  have : toEnd R L (LieModule.genWeightSpace M χ) x - algebraMap R _ (χ x) =
      (toEnd R L M x - algebraMap R _ (χ x)).restrict
        (fun m hm ↦ sub_mem (LieSubmodule.lie_mem _ hm) (Submodule.smul_mem _ _ hm)) := by
    rfl
  obtain ⟨k, hk⟩ := LieModule.exists_genWeightSpace_le_ker_of_isNoetherian M χ x
  use k
  ext ⟨m, hm⟩
  simp only [this, Module.End.pow_restrict _, LinearMap.zero_apply, ZeroMemClass.coe_zero,
    ZeroMemClass.coe_eq_zero]
  exact ZeroMemClass.coe_eq_zero.mp (hk hm)

