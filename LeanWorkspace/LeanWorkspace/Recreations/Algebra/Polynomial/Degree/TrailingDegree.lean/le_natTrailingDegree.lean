import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_natTrailingDegree (hp : p ≠ 0) (hn : ∀ m < n, p.coeff m = 0) :
    n ≤ p.natTrailingDegree := by
  rw [Polynomial.natTrailingDegree_eq_support_min' hp]
  exact Finset.le_min' _ _ _ fun m hm => not_lt.1 fun hmn => mem_support_iff.1 hm <| hn _ hmn

