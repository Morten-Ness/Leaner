import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [NonAssocSemiring R] [NonAssocSemiring S]

variable [NoZeroDivisors R] [CharZero R] {a : R}

theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero, false_or]

