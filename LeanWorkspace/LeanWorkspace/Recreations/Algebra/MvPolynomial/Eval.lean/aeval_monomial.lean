import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem aeval_monomial (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ k := MvPolynomial.eval₂Hom_monomial _ _ _ _

