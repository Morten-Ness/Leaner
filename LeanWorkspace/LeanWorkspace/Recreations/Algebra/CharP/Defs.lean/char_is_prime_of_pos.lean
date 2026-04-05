import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero R _).resolve_right <| NeZero.ne p⟩

