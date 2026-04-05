import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S] (f : R →+* S)

theorem vars_map : (map f p).vars ⊆ p.vars := by
  classical simp [MvPolynomial.vars_def, Multiset.subset_of_le degrees_map_le]

