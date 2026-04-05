import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_mem_support_of_nonzero (H : p ≠ 0) : p.natDegree ∈ p.support := by
  rw [mem_support_iff]
  exact (not_congr leadingCoeff_eq_zero).mpr H

