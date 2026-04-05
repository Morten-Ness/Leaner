import Mathlib

variable {α R M M₂ : Type*}

theorem support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support g := fun x hbf hf ↦ hbf <| by rw [Pi.smul_apply', hf, smul_zero]

