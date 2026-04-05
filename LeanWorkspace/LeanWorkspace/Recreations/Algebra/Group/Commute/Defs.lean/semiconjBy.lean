import Mathlib

variable {G M S : Type*}

variable [Mul S]

theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b := h

