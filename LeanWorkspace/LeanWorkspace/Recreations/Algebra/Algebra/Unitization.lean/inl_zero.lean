import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_zero [Zero R] [Zero A] : (Unitization.inl 0 : Unitization R A) = 0 := rfl

