import Mathlib

variable {l m n R S A : Type*}

variable [Semiring R] [Semiring S] [NonUnitalNonAssocSemiring A]

variable [Module R A] [Module S A]

variable [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

theorem Matrix.vecMulBilin_apply [Fintype m] (v : m → A) (M : Matrix m n A) :
    Matrix.vecMulBilin R S v M = v ᵥ* M := rfl

example {A} [Semiring A] [Fintype m] := (vecMulBilin A Aᵐᵒᵖ : _ →ₗ[_] Matrix m n A →ₗ[_] _)

