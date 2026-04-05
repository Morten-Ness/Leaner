import Mathlib

open scoped Algebra

variable {R : Type*} [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m := (algebra_compatible_smul A r m).symm

