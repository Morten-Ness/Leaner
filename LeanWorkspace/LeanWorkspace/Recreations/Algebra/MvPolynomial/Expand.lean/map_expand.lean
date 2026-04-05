import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem map_expand (f : R →+* S) (φ : MvPolynomial σ R) :
    map f (MvPolynomial.expand p φ) = MvPolynomial.expand p (map f φ) := by simp [MvPolynomial.expand, map_bind₁]

