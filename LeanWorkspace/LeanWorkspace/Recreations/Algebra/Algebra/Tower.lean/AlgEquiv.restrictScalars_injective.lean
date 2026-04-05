import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_injective :
    Function.Injective (AlgEquiv.restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun _ _ h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h :)

