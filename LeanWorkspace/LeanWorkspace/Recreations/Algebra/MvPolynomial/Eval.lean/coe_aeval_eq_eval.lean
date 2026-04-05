import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem coe_aeval_eq_eval :
    RingHomClass.toRingHom (MvPolynomial.aeval f : MvPolynomial σ S₁ →ₐ[S₁] S₁) = MvPolynomial.eval f := rfl

