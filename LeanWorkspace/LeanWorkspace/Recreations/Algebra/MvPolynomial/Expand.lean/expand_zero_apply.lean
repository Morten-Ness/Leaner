import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_zero_apply (f : MvPolynomial σ R) : MvPolynomial.expand 0 f = .C (MvPolynomial.eval 1 f) := by
  simp

