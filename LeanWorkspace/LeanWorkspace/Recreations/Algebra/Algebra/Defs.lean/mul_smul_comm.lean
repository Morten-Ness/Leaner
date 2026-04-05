import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.left_comm]

