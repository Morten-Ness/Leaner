import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable {S A B} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem restrictScalars_top : Subalgebra.restrictScalars R (⊤ : Subalgebra S A) = ⊤ := by
  ext x
  simp [Subalgebra.restrictScalars]
