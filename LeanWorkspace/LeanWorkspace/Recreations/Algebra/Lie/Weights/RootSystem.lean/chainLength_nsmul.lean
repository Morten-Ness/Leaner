import Mathlib

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

variable (α β : Weight K H L)

set_option backward.privateInPublic true in
private theorem chainLength_aux (hα : α.IsNonZero) {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    ∃ n : ℕ, n • x = ⁅coroot α, x⁆ := by
  by_cases hx' : x = 0
  · exact ⟨0, by simp [hx']⟩
  obtain ⟨h, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  obtain rfl := isSl2.h_eq_coroot hα he hf
  have : isSl2.HasPrimitiveVectorWith x (chainTop α β (coroot α)) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hx
    ⟨hx', by rw [← lie_eq_smul_of_mem_rootSpace hx]; rfl,
      by rwa [genWeightSpace_add_chainTop α β hα] at this⟩
  obtain ⟨μ, hμ⟩ := this.exists_nat
  exact ⟨μ, by rw [← Nat.cast_smul_eq_nsmul K, ← hμ, lie_eq_smul_of_mem_rootSpace hx]⟩


theorem chainLength_nsmul {x} (hx : x ∈ rootSpace H (chainTop α β)) :
    LieAlgebra.IsKilling.chainLength α β • x = ⁅coroot α, x⁆ := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, LieAlgebra.IsKilling.chainLength_of_isZero _ _ hα, zero_smul, zero_lie]
  let x' := (chainTop α β).exists_ne_zero.choose
  have h : x' ∈ rootSpace H (chainTop α β) ∧ x' ≠ 0 :=
    (chainTop α β).exists_ne_zero.choose_spec
  obtain ⟨k, rfl⟩ : ∃ k : K, k • x' = x := by
    simpa using (finrank_eq_one_iff_of_nonzero' ⟨x', h.1⟩ (by simpa using h.2)).mp
      (finrank_rootSpace_eq_one _ (chainTop_isNonZero α β hα)) ⟨_, hx⟩
  rw [lie_smul, smul_comm, LieAlgebra.IsKilling.chainLength, dif_neg hα, (chainLength_aux α β hα h.1).choose_spec]

