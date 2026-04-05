import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Div (G i)]

theorem div_apply (f g : ∀ i, G i) (i : ι) : (f / g) i = f i / g i := rfl

