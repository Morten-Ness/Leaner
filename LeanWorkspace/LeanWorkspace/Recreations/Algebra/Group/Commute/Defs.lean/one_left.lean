import Mathlib

variable {G M S : Type*}

variable [MulOneClass M]

theorem one_left (a : M) : Commute 1 a := SemiconjBy.one_left a

