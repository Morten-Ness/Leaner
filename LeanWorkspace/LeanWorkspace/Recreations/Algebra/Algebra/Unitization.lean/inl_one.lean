import Mathlib

variable {R A : Type*}

theorem inl_one [One R] [Zero A] : (Unitization.inl 1 : Unitization R A) = 1 := rfl

