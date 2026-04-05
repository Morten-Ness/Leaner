import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem ne_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (Polynomial.eraseLead f).support) :
    a ≠ f.natDegree := (Polynomial.lt_natDegree_of_mem_eraseLead_support h).ne

