import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_prod_X_pow [DecidableEq σ] (d : σ →₀ ℕ) (x : σ → ℕ) (s : Finset σ) :
    MvPolynomial.coeff d (∏ y ∈ s, (MvPolynomial.X y : MvPolynomial σ R) ^ x y) =
      if d = Finsupp.indicator s (fun i _ ↦ x i) then 1 else 0 := by
  simp_rw [MvPolynomial.prod_X_pow x s, MvPolynomial.coeff_monomial, eq_comm]

