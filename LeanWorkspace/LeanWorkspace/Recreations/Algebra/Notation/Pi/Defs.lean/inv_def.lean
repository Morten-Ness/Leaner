import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Inv (G i)]

theorem inv_def (f : ∀ i, G i) : f⁻¹ = fun i ↦ (f i)⁻¹ := rfl

