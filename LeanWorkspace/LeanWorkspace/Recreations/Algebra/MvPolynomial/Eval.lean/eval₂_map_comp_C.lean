import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval₂_map_comp_C {ι : Type*} (f : R →+* S₁) (h : ι → MvPolynomial σ S₁)
    (p : MvPolynomial ι R) : MvPolynomial.eval₂ ((MvPolynomial.map f).comp C) h p = MvPolynomial.eval₂ C h (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

