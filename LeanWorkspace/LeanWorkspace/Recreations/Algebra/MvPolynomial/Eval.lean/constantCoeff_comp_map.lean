import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem constantCoeff_comp_map (f : R →+* S₁) :
    (constantCoeff : MvPolynomial σ S₁ →+* S₁).comp (MvPolynomial.map f) =
      f.comp constantCoeff := by
  ext <;> simp

