import Mathlib

open scoped symmDiff

variable {ι : Sort*} {α M : Type*}

variable [CommGroup M] [Lattice M]

theorem mabs_mulIndicator_symmDiff (s t : Set α) (f : α → M) (x : α) :
    |mulIndicator (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ := apply_mulIndicator_symmDiff mabs_inv s t f x

