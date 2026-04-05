import Mathlib

variable {R R' S M M' : Type*}

variable {R A : Type*} [Semiring R]

variable (R A) [NonUnitalSemiring A] [Module R A]

theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

