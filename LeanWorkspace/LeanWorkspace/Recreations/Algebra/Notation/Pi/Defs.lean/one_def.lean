import Mathlib

variable {ι α β : Type*} {G M R : ι → Type*}

variable [∀ i, One (M i)]

theorem one_def : (1 : ∀ i, M i) = fun _ ↦ 1 := rfl

