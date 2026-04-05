import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

theorem nextCoeff_ne_zero : p.nextCoeff ≠ 0 ↔ p.natDegree ≠ 0 ∧ p.coeff (p.natDegree - 1) ≠ 0 := by
  simp [Polynomial.nextCoeff]

