import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_eq_natTrailingDegree (hp : p ≠ 0) :
    Polynomial.trailingDegree p = (Polynomial.natTrailingDegree p : ℕ∞) := .symm <| ENat.coe_toNat <| mt Polynomial.trailingDegree_eq_top.1 hp

