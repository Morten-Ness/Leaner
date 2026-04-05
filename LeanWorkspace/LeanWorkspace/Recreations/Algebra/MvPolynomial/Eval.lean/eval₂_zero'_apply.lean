import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem eval₂_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    MvPolynomial.eval₂ f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) := MvPolynomial.eval₂_zero_apply f p

