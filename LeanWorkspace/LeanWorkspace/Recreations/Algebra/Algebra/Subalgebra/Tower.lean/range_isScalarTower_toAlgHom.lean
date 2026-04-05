import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

theorem range_isScalarTower_toAlgHom [CommSemiring R] [CommSemiring A]
    [Algebra R A] (S : Subalgebra R A) :
    LinearMap.range (IsScalarTower.toAlgHom R S A : S →ₗ[R] A) = Subalgebra.toSubmodule S := by
  ext
  simp [algebraMap_eq]

