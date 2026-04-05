import Mathlib

variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

theorem neg_right (h : Associated a b) : Associated a (-b) := Associated.neg_left h.symm.symm

