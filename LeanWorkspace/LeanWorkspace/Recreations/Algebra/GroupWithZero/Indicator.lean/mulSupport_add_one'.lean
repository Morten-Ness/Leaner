import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [One R]

theorem mulSupport_add_one' [AddRightCancelMonoid R] (f : ι → R) : mulSupport (f + 1) = support f := Function.mulSupport_add_one f

