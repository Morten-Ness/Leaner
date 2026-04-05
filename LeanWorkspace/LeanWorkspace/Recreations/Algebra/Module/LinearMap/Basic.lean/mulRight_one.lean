import Mathlib

variable {R R' S M M' : Type*}

variable {R A : Type*} [Semiring R]

variable [NonAssocSemiring A] [Module R A]

theorem mulRight_one [IsScalarTower R A A] : mulRight R (1 : A) = LinearMap.id := ext mul_one

