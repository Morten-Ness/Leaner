import Mathlib

variable {G M S : Type*}

variable [MulOneClass M]

theorem one_right (a : M) : Commute a 1 := SemiconjBy.one_right a

