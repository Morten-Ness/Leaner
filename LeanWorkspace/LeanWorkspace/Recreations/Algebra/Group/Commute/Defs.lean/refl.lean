import Mathlib

variable {G M S : Type*}

variable [Mul S]

theorem refl (a : S) : Commute a a := Eq.refl (a * a)

