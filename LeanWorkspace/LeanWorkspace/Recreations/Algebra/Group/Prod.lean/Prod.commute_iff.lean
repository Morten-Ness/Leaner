import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Mul M] [Mul N]

theorem Prod.commute_iff {x y : M × N} :
    Commute x y ↔ Commute x.1 y.1 ∧ Commute x.2 y.2 := semiconjBy_iff

