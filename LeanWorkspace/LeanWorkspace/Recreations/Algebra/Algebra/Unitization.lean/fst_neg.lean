import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem fst_neg [Neg R] [Neg A] (x : Unitization R A) : (-x).fst = -x.fst := rfl

