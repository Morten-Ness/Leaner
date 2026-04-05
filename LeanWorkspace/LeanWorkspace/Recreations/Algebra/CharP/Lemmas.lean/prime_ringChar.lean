import Mathlib

variable {R S : Type*}

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

theorem prime_ringChar : Nat.Prime (ringChar R) := by
  apply CharP.char_prime_of_ne_zero R
  exact CharP.ringChar_ne_zero_of_finite R

