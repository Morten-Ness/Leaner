import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_apply (p : R[X]) : Polynomial.derivative p = p.sum fun n a => Polynomial.C (a * n) * Polynomial.X ^ (n - 1) := rfl

