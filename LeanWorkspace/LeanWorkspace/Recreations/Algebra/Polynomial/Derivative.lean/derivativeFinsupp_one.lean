import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivativeFinsupp_one : Polynomial.derivativeFinsupp (1 : R[X]) = .single 0 1 := by
  simpa using Polynomial.derivativeFinsupp_C (1 : R)

