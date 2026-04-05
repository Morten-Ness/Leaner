import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem coe_expand : (Polynomial.expand R p : R[X] → R[X]) = eval₂ Polynomial.C (Polynomial.X ^ p) := rfl

