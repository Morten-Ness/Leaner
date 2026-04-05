import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem extendScalarsOfSurjective_symm (h : Function.Surjective (algebraMap R S))
    (f : A ≃ₐ[R] B) :
    (f.extendScalarsOfSurjective h).symm = f.symm.extendScalarsOfSurjective h := rfl

