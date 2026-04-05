import Mathlib

variable {G M S : Type*}

variable [Mul S]

theorem symm {a b : S} (h : Commute a b) : Commute b a := Eq.symm h

