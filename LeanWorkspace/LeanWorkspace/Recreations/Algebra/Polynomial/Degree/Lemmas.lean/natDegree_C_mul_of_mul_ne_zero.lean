import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) :
    (Polynomial.C a * p).natDegree = p.natDegree := by
  refine Polynomial.eq_natDegree_of_le_mem_support (Polynomial.natDegree_C_mul_le a p) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_C_mul]

