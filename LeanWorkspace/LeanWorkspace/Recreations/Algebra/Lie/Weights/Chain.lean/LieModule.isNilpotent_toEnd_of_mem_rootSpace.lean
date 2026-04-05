import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {K : Type*} [Field K] [CharZero K] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [Module K M] [LieModule K L M]
  [IsTriangularizable K H M] [FiniteDimensional K M]

theorem LieModule.isNilpotent_toEnd_of_mem_rootSpace
    {x : L} {χ : H → K} (hχ : χ ≠ 0) (hx : x ∈ rootSpace H χ) :
    _root_.IsNilpotent (toEnd K L M x) := by
  refine Module.End.isNilpotent_iff_of_finite.mpr fun m ↦ ?_
  have hm : m ∈ ⨆ χ : LieModule.Weight K H M, genWeightSpace M χ := by
    simp [iSup_genWeightSpace_eq_top' K H M]
  induction hm using LieSubmodule.iSup_induction' with
  | zero => exact ⟨0, map_zero _⟩
  | mem χ₂ m₂ hm₂ =>
    obtain ⟨n, -, hn⟩ := LieModule.exists_genWeightSpace_smul_add_eq_bot M χ χ₂ hχ
    use n
    have := toEnd_pow_apply_mem hx hm₂ n
    rwa [hn, LieSubmodule.mem_bot] at this
  | add m₁ m₂ hm₁ hm₂ hm₁' hm₂' =>
    obtain ⟨n₁, hn₁⟩ := hm₁'
    obtain ⟨n₂, hn₂⟩ := hm₂'
    refine ⟨max n₁ n₂, ?_⟩
    rw [map_add, Module.End.pow_map_zero_of_le le_sup_left hn₁,
      Module.End.pow_map_zero_of_le le_sup_right hn₂, add_zero]

