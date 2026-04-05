import Mathlib

variable {R R' S M M' : Type*}

variable {R A : Type*} [Semiring R]

variable [NonAssocSemiring A] [Module R A]

theorem mulRight_eq_zero_iff [IsScalarTower R A A] (a : A) : mulRight R a = 0 ↔ a = 0 := mulRight_zero_eq_zero R A ▸ mulRight_inj

