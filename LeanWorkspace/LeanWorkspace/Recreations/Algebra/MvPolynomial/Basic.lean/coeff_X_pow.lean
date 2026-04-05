import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_X_pow [DecidableEq σ] (i : σ) (m) (k : ℕ) :
    MvPolynomial.coeff m (MvPolynomial.X i ^ k : MvPolynomial σ R) = if Finsupp.single i k = m then 1 else 0 := by
  have := MvPolynomial.coeff_monomial m (Finsupp.single i k) (1 : R)
  rwa [@MvPolynomial.monomial_eq _ _ (1 : R) (Finsupp.single i k) _, MvPolynomial.C_1, one_mul, Finsupp.prod_single_index]
    at this
  exact pow_zero _

