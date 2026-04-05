import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_eval₂ (f : R →+* S₁) (g : S₂ → MvPolynomial S₃ R) (p : MvPolynomial S₂ R) :
    MvPolynomial.map f (MvPolynomial.eval₂ C g p) = MvPolynomial.eval₂ C (MvPolynomial.map f ∘ g) (MvPolynomial.map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [MvPolynomial.eval₂_C, MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.eval₂_C]
  · intro p q hp hq
    rw [MvPolynomial.eval₂_add, (MvPolynomial.map f).map_add, hp, hq, (MvPolynomial.map f).map_add, MvPolynomial.eval₂_add]
  · intro p s hp
    rw [MvPolynomial.eval₂_mul, (MvPolynomial.map f).map_mul, hp, (MvPolynomial.map f).map_mul, MvPolynomial.map_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
      comp_apply]

