import Mathlib

variable {α G M : Type*}

variable {M : Type*}

variable (f g : ℕ → M) {m n : ℕ}

variable [CommGroup M]

theorem prod_Ico_div (hmn : m ≤ n) : ∏ i ∈ Ico m n, f (i + 1) / f i = f n / f m := by
  rw [Finset.prod_Ico_eq_div _ hmn, prod_range_div, prod_range_div, div_div_div_cancel_right]

