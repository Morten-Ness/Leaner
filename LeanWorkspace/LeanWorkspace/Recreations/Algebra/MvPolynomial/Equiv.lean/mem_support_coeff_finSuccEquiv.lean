import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ ((MvPolynomial.finSuccEquiv R n f).coeff i).support ↔ m.cons i ∈ f.support := by
  apply Iff.intro
  · intro h
    simpa [← MvPolynomial.finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← MvPolynomial.finSuccEquiv_coeff_coeff m f i] using h

