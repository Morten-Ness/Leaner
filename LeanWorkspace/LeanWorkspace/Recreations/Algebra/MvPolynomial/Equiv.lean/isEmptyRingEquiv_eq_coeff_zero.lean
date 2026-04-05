import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable [IsEmpty σ]

theorem isEmptyRingEquiv_eq_coeff_zero {σ R : Type*} [CommSemiring R] [IsEmpty σ] {x} :
    MvPolynomial.isEmptyRingEquiv R σ x = x.coeff 0 := by
  obtain ⟨x, rfl⟩ := (MvPolynomial.isEmptyRingEquiv R σ).symm.surjective x; simp

