import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [One R]

theorem mulSupport_one_sub [AddGroup R] (f : ι → R) :
    mulSupport (fun x ↦ 1 - f x) = support f := Function.mulSupport_one_sub' f

