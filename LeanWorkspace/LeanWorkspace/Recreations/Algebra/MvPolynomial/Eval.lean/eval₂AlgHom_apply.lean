import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

variable [Algebra R S₁] (g : σ → S₁)

theorem eval₂AlgHom_apply (P : MvPolynomial σ R) :
    MvPolynomial.eval₂AlgHom R g P = MvPolynomial.eval₂Hom (algebraMap R S₁) g P := rfl

