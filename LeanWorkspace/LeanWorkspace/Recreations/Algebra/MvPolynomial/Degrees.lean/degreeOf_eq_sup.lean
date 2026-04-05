import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_eq_sup (n : σ) (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf n f = f.support.sup fun m => m n := by
  classical
  rw [MvPolynomial.degreeOf_def, MvPolynomial.degrees, Multiset.count_finset_sup]
  congr
  ext
  simp only [count_toMultiset]

