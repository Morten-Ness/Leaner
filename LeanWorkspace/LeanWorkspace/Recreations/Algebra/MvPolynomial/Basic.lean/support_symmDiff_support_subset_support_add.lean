import Mathlib

open scoped Pointwise symmDiff

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_symmDiff_support_subset_support_add [DecidableEq σ] (p q : MvPolynomial σ R) :
    p.support ∆ q.support ⊆ (p + q).support := by
  rw [symmDiff_def, Finset.sup_eq_union]
  apply Finset.union_subset
  · exact MvPolynomial.support_sdiff_support_subset_support_add p q
  · rw [add_comm]
    exact MvPolynomial.support_sdiff_support_subset_support_add q p

