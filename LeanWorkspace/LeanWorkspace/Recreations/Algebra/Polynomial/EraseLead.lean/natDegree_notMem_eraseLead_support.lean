import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_notMem_eraseLead_support : f.natDegree ∉ (Polynomial.eraseLead f).support := fun h =>
  Polynomial.ne_natDegree_of_mem_eraseLead_support h rfl

