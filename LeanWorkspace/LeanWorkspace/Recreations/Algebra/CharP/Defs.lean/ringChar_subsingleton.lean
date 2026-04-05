import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem ringChar_subsingleton [Subsingleton R] : ringChar R = 1 := by simpa

