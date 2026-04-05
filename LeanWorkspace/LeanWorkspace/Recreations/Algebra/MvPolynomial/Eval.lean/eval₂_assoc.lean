import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_assoc (q : S₂ → MvPolynomial σ R) (p : MvPolynomial S₂ R) :
    MvPolynomial.eval₂ f (fun t => MvPolynomial.eval₂ f g (q t)) p = MvPolynomial.eval₂ f g (MvPolynomial.eval₂ C q p) := by
  change _ = MvPolynomial.eval₂Hom f g (MvPolynomial.eval₂ C q p)
  rw [MvPolynomial.eval₂_comp_left (MvPolynomial.eval₂Hom f g)]; congr with a; simp

