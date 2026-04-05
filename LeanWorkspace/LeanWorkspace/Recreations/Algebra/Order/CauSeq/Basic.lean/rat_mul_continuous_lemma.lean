import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  (abv : β → α) [IsAbsoluteValue abv]

theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ →
      abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε := by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => ?_⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))
  set M := max 1 (max K₁ K₂)
  have : abv (a₁ - b₁) * abv b₂ + abv (a₂ - b₂) * abv a₁ < ε / 2 / M * M + ε / 2 / M * M := by
    gcongr
  rw [← abv_mul abv, mul_comm, div_mul_cancel₀ _ (ne_of_gt K0), ← abv_mul abv, add_halves] at this
  simpa [sub_eq_add_neg, mul_add, add_mul, add_left_comm] using
    lt_of_le_of_lt (abv_add abv _ _) this

