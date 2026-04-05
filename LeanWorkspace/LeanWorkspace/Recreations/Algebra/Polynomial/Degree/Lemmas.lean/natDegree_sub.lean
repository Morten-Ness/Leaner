import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Ring R] {p q : R[X]}

theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← natDegree_neg, neg_sub]

