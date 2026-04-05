import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_one : MvPolynomial.expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 i
  simp

