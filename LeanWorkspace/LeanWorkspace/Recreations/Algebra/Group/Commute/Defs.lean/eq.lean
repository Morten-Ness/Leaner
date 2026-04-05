import Mathlib

variable {G M S : Type*}

variable [Mul S]

theorem eq {a b : S} (h : Commute a b) : a * b = b * a := h

