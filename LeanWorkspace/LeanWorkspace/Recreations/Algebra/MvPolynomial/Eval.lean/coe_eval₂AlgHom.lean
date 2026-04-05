import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

variable [Algebra R S₁] (g : σ → S₁)

theorem coe_eval₂AlgHom : ⇑(MvPolynomial.eval₂AlgHom R g) = MvPolynomial.eval₂ (algebraMap R S₁) g := rfl

