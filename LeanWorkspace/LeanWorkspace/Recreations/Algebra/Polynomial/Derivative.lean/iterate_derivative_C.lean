import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_C {k} (h : 0 < k) : Polynomial.derivative^[k] (Polynomial.C a : R[X]) = 0 := Polynomial.iterate_derivative_eq_zero <| (natDegree_C _).trans_lt h

