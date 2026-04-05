import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem natDegree_divX_le : p.divX.natDegree ≤ p.natDegree := Polynomial.natDegree_divX_eq_natDegree_tsub_one.trans_le (Nat.pred_le _)

