import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_eq_preimage (f : ι → M) : Function.mulSupport f = f ⁻¹' {1}ᶜ := rfl

