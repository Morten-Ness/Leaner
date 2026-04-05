import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_def [DecidableEq σ] (i : σ) : MvPolynomial.pderiv i = mkDerivation R (Pi.single i 1) := by
  unfold MvPolynomial.pderiv; congr!

