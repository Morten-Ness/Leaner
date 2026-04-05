import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval₂Hom_map_hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : MvPolynomial.eval₂Hom φ g (MvPolynomial.map f p) = MvPolynomial.eval₂Hom (φ.comp f) g p := MvPolynomial.eval₂_map f g φ p

