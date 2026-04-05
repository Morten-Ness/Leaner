import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable [IsEmpty σ]

theorem isEmptyRingEquiv_symm_toRingHom : (MvPolynomial.isEmptyRingEquiv R σ).symm.toRingHom = Polynomial.C := rfl

