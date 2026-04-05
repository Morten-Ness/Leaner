import Mathlib

variable {R S : Type*}

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

theorem char_is_prime (p : ℕ) [CharP R p] : p.Prime := Or.resolve_right (char_is_prime_or_zero R p) (CharP.char_ne_zero_of_finite R p)

