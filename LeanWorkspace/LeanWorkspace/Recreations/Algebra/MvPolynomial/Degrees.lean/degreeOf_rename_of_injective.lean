import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f)
    (i : σ) : MvPolynomial.degreeOf (f i) (rename f p) = MvPolynomial.degreeOf i p := by
  classical
  simp only [MvPolynomial.degreeOf, MvPolynomial.degrees_rename_of_injective h, Multiset.count_map_eq_count' f p.degrees h]

