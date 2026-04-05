import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_lt_iff_degree_lt (hp : p ≠ 0) : p.natDegree < n ↔ p.degree < ↑n := WithBot.unbotD_lt_iff (absurd · (Polynomial.degree_eq_bot.not.mpr hp))

alias ⟨degree_le_of_natDegree_le, natDegree_le_of_degree_le⟩ := Polynomial.natDegree_le_iff_degree_le

