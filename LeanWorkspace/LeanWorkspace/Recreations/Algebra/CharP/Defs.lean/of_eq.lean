import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem of_eq {p : ℕ} (h : ringChar R = p) : CharP R p := CharP.congr (ringChar R) h

