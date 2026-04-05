import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem coeff_expand_smul (hp : p ≠ 0) (φ : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (MvPolynomial.expand p φ).coeff (p • m) = φ.coeff m := by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

