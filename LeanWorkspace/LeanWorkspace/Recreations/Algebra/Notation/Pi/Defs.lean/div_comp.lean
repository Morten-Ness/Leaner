import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Div (G i)]

variable {G : Type*} [Div G]

theorem div_comp (f g : β → G) (z : α → β) : (f / g) ∘ z = f ∘ z / g ∘ z := rfl

