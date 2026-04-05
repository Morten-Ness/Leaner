import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [One R]

theorem mulSupport_add_one [AddRightCancelMonoid R] (f : ι → R) :
    mulSupport (fun x ↦ f x + 1) = support f := Set.ext fun _ ↦ not_congr add_eq_right

