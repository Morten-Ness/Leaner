import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Pow (M i) α]

variable {M : Type*} [Pow M α]

theorem pow_comp (f : β → M) (a : α) (g : ι → β) : (f ^ a) ∘ g = f ∘ g ^ a := rfl

