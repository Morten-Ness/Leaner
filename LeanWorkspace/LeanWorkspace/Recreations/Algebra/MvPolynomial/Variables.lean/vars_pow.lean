import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem vars_pow (φ : MvPolynomial σ R) (n : ℕ) : (φ ^ n).vars ⊆ φ.vars := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    apply Finset.Subset.trans (MvPolynomial.vars_mul _ _)
    exact Finset.union_subset (Finset.Subset.refl _) ih

