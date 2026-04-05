import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem eq (p : ℕ) [C : CharP R p] : ringChar R = p := ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm

