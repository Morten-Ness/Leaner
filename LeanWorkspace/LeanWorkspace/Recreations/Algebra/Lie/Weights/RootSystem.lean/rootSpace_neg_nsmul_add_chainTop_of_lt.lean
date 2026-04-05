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


theorem rootSpace_neg_nsmul_add_chainTop_of_lt (hα : α.IsNonZero) {n : ℕ} (hn : LieAlgebra.IsKilling.chainLength α β < n) :
    rootSpace H (-(n • α) + chainTop α β) = ⊥ := by
  by_contra e
  let W : Weight K H L := ⟨_, e⟩
  have hW : (W : H → K) = -(n • α) + chainTop α β := rfl
  have H₁ : 1 + n + chainTopCoeff (-α) W ≤ LieAlgebra.IsKilling.chainLength (-α) W := by
    have := LieAlgebra.IsKilling.apply_coroot_eq_cast' (-α) W
    simp only [coroot_neg, map_neg, hW, nsmul_eq_mul, Pi.natCast_def, coe_chainTop, zsmul_eq_mul,
      Int.cast_natCast, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, root_apply_coroot hα, mul_two,
      LieAlgebra.IsKilling.apply_coroot_eq_cast' α β, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, mul_comm (2 : K),
      add_sub_cancel, add_sub, Nat.cast_inj, eq_sub_iff_add_eq, ← Nat.cast_add, ← sub_eq_neg_add,
      sub_eq_iff_eq_add] at this
    lia
  have H₂ : ((1 + n + chainTopCoeff (-α) W) • α + chainTop (-α) W : H → K) =
      (chainTopCoeff α β + 1) • α + β := by
    simp only [Weight.coe_neg, ← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_add, Nat.cast_one, coe_chainTop,
      smul_neg, ← neg_smul, hW, ← add_assoc, ← add_smul, ← sub_eq_add_neg]
    congr 2
    ring
  have := LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_le (-α) W H₁
  rw [Weight.coe_neg, ← smul_neg, neg_neg, ← Weight.coe_neg, H₂] at this
  exact this (genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα)

