import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [Nontrivial R]

theorem expChar_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by
  constructor
  · rintro rfl
    exact char_zero_of_expChar_one R p
  · rintro rfl
    exact expChar_one_of_char_zero R q

