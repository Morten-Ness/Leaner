import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Inv (G i)]

theorem inv_apply (f : ∀ i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹ := rfl

