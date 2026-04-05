import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_le_iff_degree_le {n : ℕ} : Polynomial.natDegree p ≤ n ↔ Polynomial.degree p ≤ n := WithBot.unbotD_le_iff (fun _ ↦ bot_le)

