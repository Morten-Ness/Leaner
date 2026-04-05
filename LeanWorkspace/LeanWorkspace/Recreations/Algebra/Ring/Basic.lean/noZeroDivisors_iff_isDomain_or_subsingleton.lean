import Mathlib

variable {R S : Type*}

theorem noZeroDivisors_iff_isDomain_or_subsingleton [Ring α] :
    NoZeroDivisors α ↔ IsDomain α ∨ Subsingleton α := by
  rw [← isCancelMulZero_iff_noZeroDivisors, isCancelMulZero_iff_isDomain_or_subsingleton]

