import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem degreeOf_neg (i : σ) (p : MvPolynomial σ R) : degreeOf i (-p) = degreeOf i p := by
  rw [degreeOf, degreeOf, MvPolynomial.degrees_neg]

