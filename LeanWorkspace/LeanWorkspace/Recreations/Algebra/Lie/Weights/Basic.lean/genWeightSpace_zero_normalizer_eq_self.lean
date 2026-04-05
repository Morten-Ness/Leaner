import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem genWeightSpace_zero_normalizer_eq_self :
    (LieModule.genWeightSpace M (0 : L → R)).normalizer = LieModule.genWeightSpace M 0 := by
  refine le_antisymm ?_ (LieSubmodule.le_normalizer _)
  intro m hm
  rw [LieSubmodule.mem_normalizer] at hm
  simp only [LieModule.mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm ⊢
  intro y
  obtain ⟨k, hk⟩ := hm y y
  use k + 1
  simpa [pow_succ, Module.End.mul_eq_comp]

