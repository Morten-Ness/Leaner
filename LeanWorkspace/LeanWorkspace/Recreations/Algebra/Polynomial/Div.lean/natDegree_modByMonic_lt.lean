import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_modByMonic_lt (p : R[X]) {q : R[X]} (hmq : Polynomial.Monic q) (hq : q ≠ 1) :
    natDegree (p %ₘ q) < q.natDegree := by
  by_cases hpq : p %ₘ q = 0
  · rw [hpq, natDegree_zero, Nat.pos_iff_ne_zero]
    contrapose! hq
    exact eq_one_of_monic_natDegree_zero hmq hq
  · haveI := Nontrivial.of_polynomial_ne hpq
    exact natDegree_lt_natDegree hpq (Polynomial.degree_modByMonic_lt p hmq)

