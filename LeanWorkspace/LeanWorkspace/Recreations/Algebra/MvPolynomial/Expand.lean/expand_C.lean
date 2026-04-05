import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_C (r : R) : MvPolynomial.expand p (C r : MvPolynomial σ R) = C r := eval₂Hom_C _ _ _

