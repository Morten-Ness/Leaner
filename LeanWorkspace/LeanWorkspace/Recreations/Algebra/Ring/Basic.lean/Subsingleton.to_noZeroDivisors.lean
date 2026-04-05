import Mathlib

variable {R S : Type*}

theorem Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero _ := .inl (Subsingleton.eq_zero _)

scoped[Subsingleton] attribute [instance] Subsingleton.to_noZeroDivisors

