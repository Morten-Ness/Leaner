import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_coeff_coeff
    (p : MvPolynomial (Option σ) R) (m : ℕ) (d : σ →₀ ℕ) :
    coeff d (((MvPolynomial.optionEquivLeft R σ) p).coeff m) = p.coeff (d.optionElim m) := by
  rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none]
  congr <;> simp

