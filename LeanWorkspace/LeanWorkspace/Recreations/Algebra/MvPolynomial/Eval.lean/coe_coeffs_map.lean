import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem coe_coeffs_map (f : R →+* S₁) (p : MvPolynomial σ R) :
    ((MvPolynomial.map f p).coeffs : Set S₁) ⊆ f '' p.coeffs := by
  classical
  exact mod_cast MvPolynomial.coeffs_map f p

