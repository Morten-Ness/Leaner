import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_comp_inr [Zero R] : TrivSqZeroExt.snd ∘ (TrivSqZeroExt.inr : M → tsze R M) = id := rfl

