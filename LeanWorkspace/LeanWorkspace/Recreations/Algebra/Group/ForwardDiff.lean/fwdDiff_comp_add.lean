import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem fwdDiff_comp_add (f : M → G) (m : M) (y : M) :
    Δ_[h] (fun r ↦ f (r + m)) y = (Δ_[h] f) (y + m) := fwdDiff_iter_comp_add h f m 1 y

