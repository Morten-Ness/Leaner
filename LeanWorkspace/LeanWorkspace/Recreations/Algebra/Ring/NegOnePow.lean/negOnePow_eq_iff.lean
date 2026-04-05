import Mathlib

theorem negOnePow_eq_iff (n₁ n₂ : ℤ) :
    n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  · rw [Int.negOnePow_even _ h₂, Int.even_sub, Int.negOnePow_eq_one_iff]
    tauto
  · rw [Int.not_even_iff_odd] at h₂
    rw [Int.negOnePow_odd _ h₂, Int.even_sub, Int.negOnePow_eq_neg_one_iff,
      ← Int.not_odd_iff_even, ← Int.not_odd_iff_even]
    tauto

