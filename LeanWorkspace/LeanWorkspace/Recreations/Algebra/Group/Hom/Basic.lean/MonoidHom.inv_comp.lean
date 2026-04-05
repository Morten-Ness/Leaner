import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

theorem inv_comp (φ : N →* G) (ψ : M →* N) : φ⁻¹.comp ψ = (φ.comp ψ)⁻¹ := rfl

