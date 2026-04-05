import Mathlib

variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

theorem neg_neg (h : Associated a b) : Associated (-a) (-b) := Associated.neg_right Associated.neg_left h

