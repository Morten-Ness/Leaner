import Mathlib

variable {α G M : Type*}

variable {M : Type*}

variable (f g : ℕ → M) {m n : ℕ}

variable [CommGroup M]

theorem prod_Icc_div (hmn : m ≤ n) (f : ℕ → M) :
    ∏ i ∈ Icc m n, f (i + 1) / f i = f (n + 1) / f m := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_div]
  omega

