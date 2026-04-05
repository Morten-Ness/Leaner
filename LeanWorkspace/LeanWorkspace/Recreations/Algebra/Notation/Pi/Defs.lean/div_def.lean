import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Div (G i)]

theorem div_def (f g : ∀ i, G i) : f / g = fun i ↦ f i / g i := rfl

