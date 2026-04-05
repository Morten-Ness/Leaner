import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem Commute.inv_sub_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]

