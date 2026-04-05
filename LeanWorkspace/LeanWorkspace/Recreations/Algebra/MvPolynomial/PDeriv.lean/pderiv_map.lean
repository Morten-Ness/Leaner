import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_map {S} [CommSemiring S] {φ : R →+* S} {f : MvPolynomial σ R} {i : σ} :
    MvPolynomial.pderiv i (map φ f) = map φ (MvPolynomial.pderiv i f) := by
  apply induction_on f (fun r ↦ by simp) (fun p q hp hq ↦ by simp [hp, hq]) fun p j eq ↦ ?_
  obtain rfl | h := eq_or_ne j i
  · simp [eq]
  · simp [eq, h]

