import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] :
    MvPolynomial.degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0 := by
  classical
  by_cases c : i = j
  · simp only [c, if_true, MvPolynomial.degreeOf_def, MvPolynomial.degrees_X, Multiset.count_singleton]
  simp [c, MvPolynomial.degreeOf_def, MvPolynomial.degrees_X]

