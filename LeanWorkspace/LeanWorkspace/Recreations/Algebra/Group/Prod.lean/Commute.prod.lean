import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Mul M] [Mul N]

theorem Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Commute x.2 y.2) : Commute x y := SemiconjBy.prod hm hn

