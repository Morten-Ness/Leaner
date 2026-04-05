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


theorem apply_coroot_eq_cast' :
    β (coroot α) = ↑(LieAlgebra.IsKilling.chainLength α β - 2 * chainTopCoeff α β : ℤ) := by
  by_cases hα : α.IsZero
  · rw [coroot_eq_zero_iff.mpr hα, LieAlgebra.IsKilling.chainLength, dif_pos hα, hα.eq, chainTopCoeff_zero, map_zero,
      CharP.cast_eq_zero, mul_zero, sub_self, Int.cast_zero]
  obtain ⟨x, hx, x_ne0⟩ := (chainTop α β).exists_ne_zero
  have := LieAlgebra.IsKilling.chainLength_smul _ _ hx
  rw [lie_eq_smul_of_mem_rootSpace hx, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero_iff_left x_ne0, sub_eq_zero, coe_chainTop', nsmul_eq_mul, Pi.natCast_def,
    Pi.add_apply, Pi.mul_apply, root_apply_coroot hα] at this
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat, eq_sub_iff_add_eq',
    this, mul_comm (2 : K)]

