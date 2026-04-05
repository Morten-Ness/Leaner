import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Mul (M i)]

theorem mul_def (f g : ∀ i, M i) : f * g = fun i ↦ f i * g i := rfl

