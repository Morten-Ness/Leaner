import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_C_mul (a : R) (p : R[X]) :
    Polynomial.derivative (Polynomial.C a * p) = Polynomial.C a * Polynomial.derivative p := Polynomial.iterate_derivative_C_mul _ _ 1

