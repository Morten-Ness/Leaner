import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem nonempty_support_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f ≠ 0) :
    (MvPolynomial.optionEquivLeft R σ f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

