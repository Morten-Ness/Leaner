import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_eq_support_max' (h : p ≠ 0) :
    p.natDegree = p.support.max' (Polynomial.nonempty_support_iff.mpr h) := (le_max' _ _ <| Polynomial.natDegree_mem_support_of_nonzero h).antisymm <|
    max'_le _ _ _ Polynomial.le_natDegree_of_mem_supp

