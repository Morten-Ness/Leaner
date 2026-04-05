import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem divByMonic_eq_of_not_monic (p : R[X]) (hq : ¬Polynomial.Monic q) : p /ₘ q = 0 := dif_neg hq

