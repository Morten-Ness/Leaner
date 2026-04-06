import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime := by
  have h := CharP.char_is_prime_or_zero (R := R) p
  cases h with
  | inl hp =>
      exact ⟨hp⟩
  | inr hp0 =>
      exact (False.elim (NeZero.ne p hp0))
