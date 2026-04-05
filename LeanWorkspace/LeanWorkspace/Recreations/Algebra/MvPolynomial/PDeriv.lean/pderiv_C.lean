import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_C {i : σ} : MvPolynomial.pderiv i (C a) = 0 := derivation_C _ _

