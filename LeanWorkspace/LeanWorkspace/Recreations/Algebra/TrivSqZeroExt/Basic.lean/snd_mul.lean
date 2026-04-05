import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst := rfl

