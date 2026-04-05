import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem coeff_expand_zero (hp : p ≠ 0) (φ : MvPolynomial σ R) :
    (MvPolynomial.expand p φ).coeff 0 = φ.coeff 0 := calc (MvPolynomial.expand p φ).coeff 0 = (MvPolynomial.expand p φ).coeff (p • 0) := by rw [smul_zero]
                          _ = φ.coeff 0 := by rw [MvPolynomial.coeff_expand_smul p hp]

