import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_mul_X_of_ne {i j : σ} (f : MvPolynomial σ R) (h : i ≠ j) :
    MvPolynomial.degreeOf i (f * X j) = MvPolynomial.degreeOf i f := by
  classical
  simp only [MvPolynomial.degreeOf_eq_sup i, support_mul_X, Finset.sup_map]
  congr
  ext
  simp only [Finsupp.single, addRightEmbedding_apply, coe_mk,
    Pi.add_apply, comp_apply, Finsupp.coe_add, Pi.single_eq_of_ne h, add_zero]

