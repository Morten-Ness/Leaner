import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_one {i : σ} : MvPolynomial.pderiv i (1 : MvPolynomial σ R) = 0 := MvPolynomial.pderiv_C

