import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem eq_C_of_derivative_eq_zero [IsAddTorsionFree R] {f : R[X]} (h : Polynomial.derivative f = 0) :
    f = Polynomial.C (f.coeff 0) := eq_C_of_natDegree_eq_zero <| Polynomial.natDegree_eq_zero_of_derivative_eq_zero h

