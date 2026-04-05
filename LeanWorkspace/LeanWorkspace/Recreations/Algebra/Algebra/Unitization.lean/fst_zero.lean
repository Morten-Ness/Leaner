import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem fst_zero [Zero R] [Zero A] : (0 : Unitization R A).fst = 0 := rfl

