import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem right_comm (x : A) (r : R) (y : A) :
    x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [mul_assoc, Algebra.commutes, ← mul_assoc]

