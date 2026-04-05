import Mathlib

open scoped Algebra

variable {R : Type*} [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m := smul_comm _ _ _

