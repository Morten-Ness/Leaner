import Mathlib

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_C (r : R) : Polynomial.expand R p (Polynomial.C r) = Polynomial.C r := eval₂_C _ _

