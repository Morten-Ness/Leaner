import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem degree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degree := by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul', hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]

nonrec theorem natDegree_mul' (hp : p.Monic) (hq : q ≠ 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [natDegree_mul']
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

