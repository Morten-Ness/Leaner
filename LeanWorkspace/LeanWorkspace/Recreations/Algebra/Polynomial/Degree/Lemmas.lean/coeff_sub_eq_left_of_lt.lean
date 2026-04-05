import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Ring R] {p q : R[X]}

theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n := by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg, Polynomial.coeff_add_eq_left_of_lt dg]

