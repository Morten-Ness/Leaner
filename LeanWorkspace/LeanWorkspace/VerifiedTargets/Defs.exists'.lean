import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases CharP.char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (CharP.charP_to_charZero R)]

