import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_prime_of_ne_zero {p : ℕ} [CharP R p] (hp : p ≠ 0) : p.Prime := by
  rcases CharP.char_is_prime_or_zero (R := R) p with hprime | hzero
  · exact hprime
  · exact (hp hzero).elim
