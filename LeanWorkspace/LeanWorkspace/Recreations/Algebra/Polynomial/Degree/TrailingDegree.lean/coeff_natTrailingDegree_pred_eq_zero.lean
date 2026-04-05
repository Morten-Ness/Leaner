import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_natTrailingDegree_pred_eq_zero {p : R[X]} {hp : (0 : ℕ∞) < Polynomial.natTrailingDegree p} :
    p.coeff (p.natTrailingDegree - 1) = 0 := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree <|
    Nat.sub_lt (WithTop.coe_pos.mp hp) Nat.one_pos

