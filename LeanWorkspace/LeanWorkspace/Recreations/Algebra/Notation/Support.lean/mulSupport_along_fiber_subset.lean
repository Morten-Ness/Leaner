import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_along_fiber_subset (f : ι × κ → M) (i : ι) :
    (Function.mulSupport fun j ↦ f (i, j)) ⊆ (Function.mulSupport f).image Prod.snd := fun j hj ↦ ⟨(i, j), by simpa using hj⟩

