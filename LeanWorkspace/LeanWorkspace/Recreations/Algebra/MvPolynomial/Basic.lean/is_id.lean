import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem is_id (f : MvPolynomial σ R →+* MvPolynomial σ R) (hC : f.comp MvPolynomial.C = MvPolynomial.C)
    (hX : ∀ n : σ, f (MvPolynomial.X n) = MvPolynomial.X n) (p : MvPolynomial σ R) : f p = p := MvPolynomial.hom_eq_hom f (RingHom.id _) hC hX p

