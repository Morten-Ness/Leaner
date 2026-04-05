import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Mul M] [Mul N]

theorem Prod.semiconjBy_iff {x y z : M × N} :
    SemiconjBy x y z ↔ SemiconjBy x.1 y.1 z.1 ∧ SemiconjBy x.2 y.2 z.2 := Prod.ext_iff

