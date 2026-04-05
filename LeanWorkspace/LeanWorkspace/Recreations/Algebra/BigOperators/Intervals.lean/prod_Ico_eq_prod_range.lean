import Mathlib

variable {α G M : Type*}

variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

theorem prod_Ico_eq_prod_range (f : ℕ → M) (m n : ℕ) :
    ∏ k ∈ Ico m n, f k = ∏ k ∈ range (n - m), f (m + k) := by
  by_cases! h : m ≤ n
  · rw [← Nat.Ico_zero_eq_range, Finset.prod_Ico_add, zero_add, tsub_add_cancel_of_le h]
  · replace h := h.le
    rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]

