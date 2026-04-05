import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem eval₂Hom_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    MvPolynomial.eval₂Hom f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) := MvPolynomial.eval₂Hom_zero_apply f p

