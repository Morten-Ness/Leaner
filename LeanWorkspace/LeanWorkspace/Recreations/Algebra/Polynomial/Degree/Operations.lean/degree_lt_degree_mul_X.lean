import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_lt_degree_mul_X (hp : p ≠ 0) : p.degree < (p * Polynomial.X).degree := by
  haveI := Nontrivial.of_polynomial_ne hp
  have : leadingCoeff p * leadingCoeff Polynomial.X ≠ 0 := by simpa
  rw [Polynomial.degree_mul' this, degree_eq_natDegree hp, degree_X, ← Nat.cast_one, ← Nat.cast_add]
  norm_cast
  exact Nat.lt_succ_self _

