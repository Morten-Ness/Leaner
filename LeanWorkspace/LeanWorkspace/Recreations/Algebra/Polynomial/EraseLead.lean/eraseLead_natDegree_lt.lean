import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_natDegree_lt (f0 : 2 ≤ #f.support) : (Polynomial.eraseLead f).natDegree < f.natDegree := lt_of_le_of_ne Polynomial.eraseLead_natDegree_le_aux <|
    Polynomial.ne_natDegree_of_mem_eraseLead_support <|
      natDegree_mem_support_of_nonzero <| Polynomial.eraseLead_ne_zero f0

