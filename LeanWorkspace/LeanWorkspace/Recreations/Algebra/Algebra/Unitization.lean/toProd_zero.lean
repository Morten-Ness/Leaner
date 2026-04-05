import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem toProd_zero [Zero R] [Zero A] : (0 : Unitization R A).toProd = 0 := rfl

