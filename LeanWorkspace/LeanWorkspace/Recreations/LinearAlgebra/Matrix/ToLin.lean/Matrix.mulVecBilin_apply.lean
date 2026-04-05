import Mathlib

variable {l m n R S A : Type*}

variable [Semiring R] [Semiring S] [NonUnitalNonAssocSemiring A]

variable [Module R A] [Module S A]

variable [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

theorem Matrix.mulVecBilin_apply [Fintype n] (M : Matrix m n A) (v : n → A) :
    Matrix.mulVecBilin R S M v = M *ᵥ v := rfl

example {A} [Semiring A] [Fintype n] := (mulVecBilin A Aᵐᵒᵖ : Matrix m n A →ₗ[_] _ →ₗ[_] _)

