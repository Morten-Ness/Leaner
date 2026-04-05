import Mathlib

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_X : Polynomial.expand R p Polynomial.X = Polynomial.X ^ p := eval₂_X _ _

