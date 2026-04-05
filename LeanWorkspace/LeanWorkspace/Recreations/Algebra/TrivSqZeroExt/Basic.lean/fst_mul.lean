import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst := rfl

