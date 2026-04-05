import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_smul {S : Type*} [SMulZeroClass S R] [IsScalarTower S R R] (s : S)
    (p : R[X]) : Polynomial.derivative (s • p) = s • Polynomial.derivative p := Polynomial.derivative.map_smul_of_tower s p

