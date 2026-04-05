import Mathlib

variable {R A : Type*}

theorem mk_toProd (x : Unitization R A) : Unitization.mk x.toProd = x := rfl

