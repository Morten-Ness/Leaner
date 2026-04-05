import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_monomial_eq (s : σ →₀ ℕ) (i : σ) {a : R} (ha : a ≠ 0) :
    (monomial s a).degreeOf i = s i := by
  classical rw [MvPolynomial.degreeOf_def, MvPolynomial.degrees_monomial_eq _ _ ha, Finsupp.count_toMultiset]

