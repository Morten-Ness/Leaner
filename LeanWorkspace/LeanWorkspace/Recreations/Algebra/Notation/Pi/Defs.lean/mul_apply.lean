import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Mul (M i)]

theorem mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl

