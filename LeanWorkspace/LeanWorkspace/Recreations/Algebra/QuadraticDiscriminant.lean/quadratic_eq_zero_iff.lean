import Mathlib

variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}

theorem quadratic_eq_zero_iff (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha, h, sq, mul_self_eq_mul_self_iff]
  field_simp
  grind

