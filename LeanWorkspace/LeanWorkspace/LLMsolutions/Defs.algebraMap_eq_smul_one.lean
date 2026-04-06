import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) := by
  rw [Algebra.smul_def]
  simp
