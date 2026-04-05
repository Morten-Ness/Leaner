import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem degree_le_zero_iff_eq_one (hp : p.Monic) : p.degree ≤ 0 ↔ p = 1 := by
  rw [← hp.natDegree_eq_zero, natDegree_eq_zero_iff_degree_le_zero]

