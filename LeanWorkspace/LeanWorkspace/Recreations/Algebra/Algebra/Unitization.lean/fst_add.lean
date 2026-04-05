import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem fst_add [Add R] [Add A] (x₁ x₂ : Unitization R A) : (x₁ + x₂).fst = x₁.fst + x₂.fst := rfl

