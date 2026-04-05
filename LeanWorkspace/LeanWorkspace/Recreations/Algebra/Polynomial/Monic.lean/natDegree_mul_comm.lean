import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p).natDegree := by
  by_cases h : q = 0
  · simp [h]
  rw [hp.natDegree_mul' h, Polynomial.natDegree_mul', add_comm]
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

