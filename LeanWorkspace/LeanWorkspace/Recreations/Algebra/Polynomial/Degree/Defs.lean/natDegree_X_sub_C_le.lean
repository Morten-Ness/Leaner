import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_X_sub_C_le (r : R) : (Polynomial.X - Polynomial.C r).natDegree ≤ 1 := Polynomial.natDegree_le_iff_degree_le.2 <| Polynomial.degree_X_sub_C_le r

