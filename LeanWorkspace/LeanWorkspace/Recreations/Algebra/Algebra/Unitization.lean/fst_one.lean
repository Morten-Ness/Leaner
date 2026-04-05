import Mathlib

variable {R A : Type*}

theorem fst_one [One R] [Zero A] : (1 : Unitization R A).fst = 1 := rfl

