import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_X {k} (h : 1 < k) : Polynomial.derivative^[k] (Polynomial.X : R[X]) = 0 := Polynomial.iterate_derivative_eq_zero <| natDegree_X_le.trans_lt h

