import Mathlib

variable {R S : Type*}

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

theorem isLeftRegular_iff_right_eq_zero_of_mul : IsLeftRegular r ↔ ∀ x, r * x = 0 → x = 0 where
  mp h r' eq := h (by simp_rw [eq, mul_zero])
  mpr h r₁ r₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [mul_sub, eq, sub_self]

