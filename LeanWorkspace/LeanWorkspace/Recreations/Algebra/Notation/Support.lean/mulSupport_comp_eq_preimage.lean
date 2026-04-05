import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_comp_eq_preimage (g : κ → M) (f : ι → κ) :
    Function.mulSupport (g ∘ f) = f ⁻¹' Function.mulSupport g := rfl

