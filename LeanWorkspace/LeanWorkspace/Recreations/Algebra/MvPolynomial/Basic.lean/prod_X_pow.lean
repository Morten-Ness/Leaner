import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem prod_X_pow (x : σ → ℕ) (t : Finset σ) :
    ∏ y ∈ t, (MvPolynomial.X y : MvPolynomial σ R) ^ x y = MvPolynomial.monomial (indicator t (fun i _ ↦ x i)) (1 : R) := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod, Finset.prod_subset (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi ↦ by simp [Finsupp.indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff, ne_eq, not_not] at hi'
    rw [hi', pow_zero]

