import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [One R]

theorem mulSupport_one_add' [AddLeftCancelMonoid R] (f : ι → R) : mulSupport (1 + f) = support f := Function.mulSupport_one_add f

