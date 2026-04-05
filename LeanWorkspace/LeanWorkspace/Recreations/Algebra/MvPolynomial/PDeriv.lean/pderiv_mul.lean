import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_mul {i : σ} {f g : MvPolynomial σ R} :
    MvPolynomial.pderiv i (f * g) = MvPolynomial.pderiv i f * g + f * MvPolynomial.pderiv i g := by
  simp only [(MvPolynomial.pderiv i).leibniz f g, smul_eq_mul, mul_comm, add_comm]

