import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub_le_iff_left (qn : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg, Polynomial.natDegree_add_le_iff_left _ _ qn]

