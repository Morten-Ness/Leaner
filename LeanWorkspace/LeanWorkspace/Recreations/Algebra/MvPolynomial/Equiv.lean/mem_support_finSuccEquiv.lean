import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (MvPolynomial.finSuccEquiv R n f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m 0) '' f.support := by
  simpa using congr(x ∈ $(MvPolynomial.support_finSuccEquiv f))

