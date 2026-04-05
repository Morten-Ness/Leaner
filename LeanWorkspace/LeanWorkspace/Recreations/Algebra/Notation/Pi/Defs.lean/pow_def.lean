import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Pow (M i) α]

theorem pow_def (f : ∀ i, M i) (a : α) : f ^ a = fun i ↦ f i ^ a := rfl

