import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem mem_support_coeff_optionEquivLeft {f : MvPolynomial (Option σ) R} {i : ℕ} {m : σ →₀ ℕ} :
    m ∈ ((MvPolynomial.optionEquivLeft R σ f).coeff i).support ↔ m.optionElim i ∈ f.support := by
  simp [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none]

