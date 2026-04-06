FAIL
import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  calc
    x * (algebraMap R A r * y) = (x * algebraMap R A r) * y := by rw [mul_assoc]
    _ = (algebraMap R A r * x) * y := by rw [mul_comm x (algebraMap R A r)]
    _ = algebraMap R A r * (x * y) := by rw [← mul_assoc]
