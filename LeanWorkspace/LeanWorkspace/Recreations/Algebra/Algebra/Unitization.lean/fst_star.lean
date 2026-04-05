import Mathlib

variable {R A : Type*}

theorem fst_star [Star R] [Star A] (x : Unitization R A) : (star x).fst = star x.fst := rfl

