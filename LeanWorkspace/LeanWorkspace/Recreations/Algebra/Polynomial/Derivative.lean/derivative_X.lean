import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_X : Polynomial.derivative (Polynomial.X : R[X]) = 1 := (Polynomial.derivative_monomial _ _).trans <| by simp

