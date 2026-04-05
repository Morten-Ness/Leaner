import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_of_natDegree_zero {p : R[X]} (hp : p.natDegree = 0) : Polynomial.derivative p = 0 := by
  rw [eq_C_of_natDegree_eq_zero hp, Polynomial.derivative_C]

