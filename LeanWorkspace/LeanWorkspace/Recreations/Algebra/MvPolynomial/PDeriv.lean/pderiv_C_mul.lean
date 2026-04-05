import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_C_mul {f : MvPolynomial σ R} {i : σ} : MvPolynomial.pderiv i (C a * f) = C a * MvPolynomial.pderiv i f := by
  rw [C_mul', Derivation.map_smul, C_mul']

