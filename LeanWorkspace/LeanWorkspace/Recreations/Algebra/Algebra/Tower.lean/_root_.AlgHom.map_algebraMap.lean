import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem _root_.AlgHom.map_algebraMap (f : A →ₐ[S] B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := by
  rw [IsScalarTower.algebraMap_apply R S A r, f.commutes, ← IsScalarTower.algebraMap_apply R S B]

