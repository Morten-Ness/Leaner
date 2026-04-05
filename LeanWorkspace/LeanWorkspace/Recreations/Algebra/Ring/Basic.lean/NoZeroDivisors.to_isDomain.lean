import Mathlib

variable {R S : Type*}

theorem NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
    IsDomain α := { NoZeroDivisors.to_isCancelMulZero α, h with .. }

