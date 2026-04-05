import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem restrictScalars_mul {A B C} [Semiring A] [Semiring B] [Semiring C]
    [SMul A B] [Module A C] [Module B C] [IsScalarTower A C C] [IsScalarTower B C C]
    [IsScalarTower A B C] {I J : Submodule B C} :
    (I * J).restrictScalars A = I.restrictScalars A * J.restrictScalars A := rfl

