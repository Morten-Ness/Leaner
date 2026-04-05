import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a ≠ 0) :
    (p * Polynomial.C a).natDegree = p.natDegree := by
  refine Polynomial.eq_natDegree_of_le_mem_support (Polynomial.natDegree_mul_C_le p a) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_mul_C]

