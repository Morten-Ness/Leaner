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


theorem eq_neg_one_or_eq_zero_or_eq_one_of_eq_smul
    (hα : α.IsNonZero) (k : K) (h : (β : H → K) = k • α) :
    k = -1 ∨ k = 0 ∨ k = 1 := by
  cases subsingleton_or_nontrivial L
  · exact IsEmpty.elim inferInstance α
  have H := LieAlgebra.IsKilling.apply_coroot_eq_cast' α β
  rw [h] at H
  simp only [Pi.smul_apply, root_apply_coroot hα] at H
  rcases (LieAlgebra.IsKilling.chainLength α β).even_or_odd with (⟨n, hn⟩ | ⟨n, hn⟩)
  · rw [hn, ← two_mul] at H
    simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, ← mul_sub, ← mul_comm (2 : K),
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at H
    rw [← Int.cast_natCast, ← Int.cast_natCast (chainTopCoeff α β), ← Int.cast_sub] at H
    have := (LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff_mem α 0 hα (n - chainTopCoeff α β)).mp
      (by rw [← Int.cast_smul_eq_zsmul K, ← H, ← h, Weight.coe_zero, add_zero]; exact β.2)
    rw [LieAlgebra.IsKilling.chainTopCoeff_zero_right α hα, LieAlgebra.IsKilling.chainBotCoeff_zero_right α hα, Nat.cast_one] at this
    set k' : ℤ := n - chainTopCoeff α β
    subst H
    have : k' ∈ ({-1, 0, 1} : Finset ℤ) := by
      change k' ∈ Finset.Icc (-1 : ℤ) (1 : ℤ)
      exact this
    simpa only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton, ← @Int.cast_inj K,
      Int.cast_zero, Int.cast_neg, Int.cast_one] using this
  · apply_fun (· / 2) at H
    rw [hn, smul_eq_mul] at H
    have hk : k = n + 2⁻¹ - chainTopCoeff α β := by simpa [sub_div, add_div] using H
    have := (LieAlgebra.IsKilling.rootSpace_zsmul_add_ne_bot_iff α β hα (chainTopCoeff α β - n)).mpr ?_
    swap
    · simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg, neg_sub, true_and]
      rw [← Nat.cast_add, LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff, hn]
      lia
    rw [h, hk, ← Int.cast_smul_eq_zsmul K, ← add_smul] at this
    simp only [Int.cast_sub, Int.cast_natCast,
      sub_add_sub_cancel', add_sub_cancel_left, ne_eq] at this
    cases this (LieAlgebra.IsKilling.rootSpace_one_div_two_smul α hα)

