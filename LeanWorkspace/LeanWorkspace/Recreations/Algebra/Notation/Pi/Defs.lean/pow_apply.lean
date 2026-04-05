import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, Pow (M i) α]

theorem pow_apply (f : ∀ i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a := rfl

