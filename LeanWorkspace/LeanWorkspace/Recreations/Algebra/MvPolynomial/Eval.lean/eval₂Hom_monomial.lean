import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂Hom_monomial (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    MvPolynomial.eval₂Hom f g (monomial d r) = f r * d.prod fun i k => g i ^ k := by
  simp only [monomial_eq, map_mul, MvPolynomial.eval₂Hom_C, Finsupp.prod, map_prod, map_pow, MvPolynomial.eval₂Hom_X']

