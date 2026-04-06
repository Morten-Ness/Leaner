import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) := by
  funext r
  rw [Algebra.smul_def, mul_one]
