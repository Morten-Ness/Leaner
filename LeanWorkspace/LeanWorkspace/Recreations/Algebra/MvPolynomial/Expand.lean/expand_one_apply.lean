import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_one_apply (f : MvPolynomial σ R) : MvPolynomial.expand 1 f = f := by simp

