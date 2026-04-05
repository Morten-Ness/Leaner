import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.fst := rfl

