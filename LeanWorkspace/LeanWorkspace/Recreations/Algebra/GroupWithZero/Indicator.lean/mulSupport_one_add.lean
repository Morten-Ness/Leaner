import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [One R]

theorem mulSupport_one_add [AddLeftCancelMonoid R] (f : ι → R) :
    mulSupport (fun x ↦ 1 + f x) = support f := Set.ext fun _ ↦ not_congr add_eq_left

