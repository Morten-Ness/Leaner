import Mathlib

variable {R S : Type*}

theorem isDomain_iff_noZeroDivisors_and_nontrivial [Ring α] :
    IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α := by
  rw [← isCancelMulZero_iff_noZeroDivisors, isDomain_iff_cancelMulZero_and_nontrivial]

