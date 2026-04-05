import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Mul (M i)]

variable {M : Type*} [Mul M]

theorem mul_comp (f g : β → M) (z : α → β) : (f * g) ∘ z = f ∘ z * g ∘ z := rfl

