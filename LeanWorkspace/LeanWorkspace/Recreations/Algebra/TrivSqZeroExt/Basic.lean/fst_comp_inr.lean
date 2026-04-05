import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_comp_inr [Zero R] : TrivSqZeroExt.fst ∘ (TrivSqZeroExt.inr : M → tsze R M) = 0 := rfl

