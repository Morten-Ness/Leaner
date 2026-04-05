import Mathlib

section

variable {R S : Type*}

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

theorem prime_ringChar : Nat.Prime (ringChar R) := by
  apply CharP.char_prime_of_ne_zero R
  exact CharP.ringChar_ne_zero_of_finite R

end

section

variable {R S : Type*}

variable (R) [NonAssocRing R]

theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 := CharP.char_ne_zero_of_finite R (ringChar R)

end
