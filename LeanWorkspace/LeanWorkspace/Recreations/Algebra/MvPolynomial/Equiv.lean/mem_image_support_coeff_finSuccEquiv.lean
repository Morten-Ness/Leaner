import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.cons i '' ((MvPolynomial.finSuccEquiv R n f).coeff i).support ↔
      x ∈ f.support ∧ x 0 = i := by
  simpa using congr(x ∈ $MvPolynomial.image_support_finSuccEquiv)

-- TODO: generalize `MvPolynomial.finSuccEquiv R n` to an arbitrary ZeroHom

