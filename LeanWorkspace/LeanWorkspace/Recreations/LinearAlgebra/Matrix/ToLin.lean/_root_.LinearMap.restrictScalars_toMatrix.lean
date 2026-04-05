import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

variable {A M n : Type*} [Fintype n] [DecidableEq n]
  [CommSemiring A] [AddCommMonoid M] [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M]
  (bA : Basis m R A) (bM : Basis n A M)

theorem _root_.LinearMap.restrictScalars_toMatrix (f : M →ₗ[A] M) :
    (f.restrictScalars R).toMatrix (bA.smulTower' bM) (bA.smulTower' bM) =
      ((f.toMatrix bM bM).map (Algebra.leftMulMatrix bA)).comp _ _ _ _ _ := by
  ext; simp [toMatrix, Algebra.leftMulMatrix_apply,
    Module.Basis.smulTower'_repr, Module.Basis.smulTower'_apply, mul_comm]

