import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem hom_eq_hom [Semiring S₂] (f g : MvPolynomial σ R →+* S₂) (hC : f.comp MvPolynomial.C = g.comp MvPolynomial.C)
    (hX : ∀ n : σ, f (MvPolynomial.X n) = g (MvPolynomial.X n)) (p : MvPolynomial σ R) : f p = g p := RingHom.congr_fun (MvPolynomial.ringHom_ext' hC hX) p

