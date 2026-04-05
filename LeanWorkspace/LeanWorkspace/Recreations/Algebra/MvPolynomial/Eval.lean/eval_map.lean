import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval_map (f : R →+* S₁) (g : σ → S₁) (p : MvPolynomial σ R) :
    MvPolynomial.eval g (MvPolynomial.map f p) = MvPolynomial.eval₂ f g p := by
  apply MvPolynomial.induction_on p <;> · simp +contextual

