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


theorem le_chainBotCoeff_of_rootSpace_ne_top
    (hα : α.IsNonZero) (n : ℤ) (hn : rootSpace H (-n • α + β) ≠ ⊥) :
    n ≤ chainBotCoeff α β := by
  contrapose! hn
  lift n to ℕ using (Nat.cast_nonneg _).trans hn.le
  rw [Nat.cast_lt, ← @Nat.add_lt_add_iff_right (chainTopCoeff α β),
    LieAlgebra.IsKilling.chainBotCoeff_add_chainTopCoeff] at hn
  have := LieAlgebra.IsKilling.rootSpace_neg_nsmul_add_chainTop_of_lt α β hα hn
  rwa [← Nat.cast_smul_eq_nsmul ℤ, ← neg_smul, coe_chainTop, ← add_assoc,
    ← add_smul, Nat.cast_add, neg_add, add_assoc, neg_add_cancel, add_zero] at this

