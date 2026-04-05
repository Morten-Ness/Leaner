import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Ring R] {p q : R[X]}

theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, Polynomial.coeff_add_eq_right_of_lt, coeff_neg]

