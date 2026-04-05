import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Inv (G i)]

variable {G : Type*} [Inv G]

theorem inv_comp (f : β → G) (g : α → β) : f⁻¹ ∘ g = (f ∘ g)⁻¹ := rfl

