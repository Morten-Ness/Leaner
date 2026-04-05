import Mathlib

variable {R A : Type*}

theorem toProd_mk (x : R × A) : toProd (Unitization.mk x) = x := rfl

