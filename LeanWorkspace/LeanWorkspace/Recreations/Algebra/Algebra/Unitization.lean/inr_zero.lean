import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Unitization R A) := rfl

