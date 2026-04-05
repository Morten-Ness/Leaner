import Mathlib

variable {R A : Type*}

theorem fst_inr [Zero R] (a : A) : (a : Unitization R A).fst = 0 := rfl

