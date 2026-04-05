import Mathlib

variable {R R' S M M' : Type*}

variable {R A : Type*} [Semiring R]

variable (R A) [NonUnitalSemiring A] [Module R A]

theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

