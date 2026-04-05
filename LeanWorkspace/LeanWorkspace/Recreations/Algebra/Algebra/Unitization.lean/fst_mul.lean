import Mathlib

variable {R A : Type*}

theorem fst_mul [Mul R] [Add A] [Mul A] [SMul R A] (x₁ x₂ : Unitization R A) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst := rfl

