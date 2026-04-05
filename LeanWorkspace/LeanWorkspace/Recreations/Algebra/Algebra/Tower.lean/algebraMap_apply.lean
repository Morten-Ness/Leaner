import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem algebraMap_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [IsScalarTower.algebraMap_eq R S A, RingHom.comp_apply]

