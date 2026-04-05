import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 := match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@CharP.char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@CharP.char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

