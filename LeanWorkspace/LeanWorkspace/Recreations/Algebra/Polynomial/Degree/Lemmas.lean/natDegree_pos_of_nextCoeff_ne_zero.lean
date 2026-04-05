import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem natDegree_pos_of_nextCoeff_ne_zero (h : p.nextCoeff ≠ 0) : 0 < p.natDegree := by
  grind [nextCoeff]

