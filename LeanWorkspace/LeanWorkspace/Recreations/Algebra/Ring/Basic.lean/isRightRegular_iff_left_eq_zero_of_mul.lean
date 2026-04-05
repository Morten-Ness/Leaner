import Mathlib

variable {R S : Type*}

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

theorem isRightRegular_iff_left_eq_zero_of_mul : IsRightRegular r ↔ ∀ x, x * r = 0 → x = 0 where
  mp h r' eq := h (by simp_rw [eq, zero_mul])
  mpr h r₁ r₂ eq := sub_eq_zero.mp <| h _ <| by simp_rw [sub_mul, eq, sub_self]

