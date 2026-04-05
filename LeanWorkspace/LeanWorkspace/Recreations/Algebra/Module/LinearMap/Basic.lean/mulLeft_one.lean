import Mathlib

variable {R R' S M M' : Type*}

variable {R A : Type*} [Semiring R]

variable [NonAssocSemiring A] [Module R A]

theorem mulLeft_one [SMulCommClass R A A] : mulLeft R (1 : A) = LinearMap.id := ext one_mul

