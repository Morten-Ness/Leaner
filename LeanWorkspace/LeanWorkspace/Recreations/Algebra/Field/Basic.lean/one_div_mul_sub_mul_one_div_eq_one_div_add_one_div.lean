import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  simpa only [one_div] using (inv_sub_inv' ha hb).symm

