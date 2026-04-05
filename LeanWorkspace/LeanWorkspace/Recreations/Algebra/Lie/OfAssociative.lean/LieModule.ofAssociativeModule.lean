import Mathlib

variable {A : Type v} [Ring A]

variable {R : Type u} [CommRing R] [Algebra R A]

variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem LieModule.ofAssociativeModule : LieModule R A M where
  smul_lie := smul_assoc
  lie_smul := smul_algebra_smul_comm

