import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, One (M i)]

theorem one_apply (i : ι) : (1 : ∀ i, M i) i = 1 := rfl

