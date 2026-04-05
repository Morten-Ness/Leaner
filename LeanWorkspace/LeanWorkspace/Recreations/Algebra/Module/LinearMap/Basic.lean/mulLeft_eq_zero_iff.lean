import Mathlib

variable {R R' S M M' : Type*}

variable {R A : Type*} [Semiring R]

variable [NonAssocSemiring A] [Module R A]

theorem mulLeft_eq_zero_iff [SMulCommClass R A A] (a : A) : mulLeft R a = 0 ↔ a = 0 := mulLeft_zero_eq_zero R A ▸ mulLeft_inj

