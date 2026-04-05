import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  simpa using not_subsingleton R

