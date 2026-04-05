import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

theorem nextCoeff_of_natDegree_pos (hp : 0 < p.natDegree) :
    Polynomial.nextCoeff p = p.coeff (p.natDegree - 1) := by
  rw [Polynomial.nextCoeff, if_neg]
  contrapose! hp
  simpa

