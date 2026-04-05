import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem card_supp_le_succ_natDegree (p : R[X]) : #p.support ≤ p.natDegree + 1 := by
  rw [← Finset.card_range (p.natDegree + 1)]
  exact Finset.card_le_card Polynomial.supp_subset_range_natDegree_succ

