import Mathlib

open scoped Algebra

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

theorem map_algebraMap_mul (f : A →ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  simpa [Algebra.smul_def] using f.map_smulₛₗ r a
