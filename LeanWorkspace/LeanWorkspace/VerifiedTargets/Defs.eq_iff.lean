import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p := ⟨ringChar.of_eq, @ringChar.eq R _ p⟩

