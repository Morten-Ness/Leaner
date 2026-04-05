import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_rightInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.RightInverse f g) :
    Function.RightInverse (MvPolynomial.map f : MvPolynomial σ R → MvPolynomial σ S₁) (MvPolynomial.map g) := (MvPolynomial.map_leftInverse hf.leftInverse).rightInverse

