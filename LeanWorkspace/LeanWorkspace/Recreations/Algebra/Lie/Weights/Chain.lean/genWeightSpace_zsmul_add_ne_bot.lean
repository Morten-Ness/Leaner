import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M]

variable (α : L → R) (β : Weight R L M)

theorem genWeightSpace_zsmul_add_ne_bot {n : ℤ}
    (hn : -LieModule.chainBotCoeff α β ≤ n) (hn' : n ≤ LieModule.chainTopCoeff α β) :
      genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact LieModule.genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul, ← smul_neg, Nat.cast_smul_eq_nsmul]
    exact LieModule.genWeightSpace_nsmul_add_ne_bot_of_le (-α) β hn

