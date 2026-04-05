import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  have : Subsingleton R := CharP.CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R

