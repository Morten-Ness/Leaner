import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem eq_one_of_monic_natDegree_zero (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1 := by
  rw [Polynomial.Monic.def, leadingCoeff, hfd] at hf
  rw [Polynomial.eq_C_of_natDegree_eq_zero hfd, hf, map_one]

