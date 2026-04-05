import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_eq_comp_X_pow {f : R[X]} : Polynomial.expand R p f = f.comp (Polynomial.X ^ p) := rfl

