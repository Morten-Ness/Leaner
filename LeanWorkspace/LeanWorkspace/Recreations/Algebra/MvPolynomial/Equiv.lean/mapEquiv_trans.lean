import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (MvPolynomial.mapEquiv σ e).trans (MvPolynomial.mapEquiv σ f) = MvPolynomial.mapEquiv σ (e.trans f) := RingEquiv.ext fun p => by
    simp only [RingEquiv.coe_trans, comp_apply, mapEquiv_apply, RingEquiv.coe_ringHom_trans,
      map_map]

