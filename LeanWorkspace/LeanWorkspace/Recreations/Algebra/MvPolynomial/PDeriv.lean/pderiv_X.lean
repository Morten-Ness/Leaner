import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_X [DecidableEq σ] (i j : σ) :
    MvPolynomial.pderiv i (X j : MvPolynomial σ R) = Pi.single (M := fun _ => _) i 1 j := by
  rw [MvPolynomial.pderiv_def, mkDerivation_X]

