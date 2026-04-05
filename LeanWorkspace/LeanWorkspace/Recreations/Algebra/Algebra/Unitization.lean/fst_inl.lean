import Mathlib

variable {R A : Type*}

theorem fst_inl [Zero A] (r : R) : (Unitization.inl r : Unitization R A).fst = r := rfl

