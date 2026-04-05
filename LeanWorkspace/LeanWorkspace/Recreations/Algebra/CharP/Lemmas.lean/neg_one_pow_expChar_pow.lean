import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hR : ExpChar R p]

theorem neg_one_pow_expChar_pow : (-1 : R) ^ p ^ n = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 2 [← one_pow (p ^ n)]
  rw [← add_pow_expChar_pow_of_commute _ _ (Commute.one_right _), neg_add_cancel,
    zero_pow (pow_ne_zero _ <| expChar_ne_zero R p)]

