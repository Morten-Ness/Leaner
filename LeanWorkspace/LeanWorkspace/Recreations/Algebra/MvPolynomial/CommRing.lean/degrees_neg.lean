import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees := by
  rw [degrees, MvPolynomial.support_neg]; rfl

