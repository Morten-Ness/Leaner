import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub_le_iff_right (pn : p.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ q.natDegree ≤ n := by rwa [Polynomial.natDegree_sub, Polynomial.natDegree_sub_le_iff_left]

