import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable {ι : Type*} (t : Finset ι) (φ : ι → MvPolynomial σ R)

theorem vars_sum_subset [DecidableEq σ] :
    (∑ i ∈ t, φ i).vars ⊆ Finset.biUnion t fun i => (φ i).vars := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ has hsum =>
    rw [Finset.biUnion_insert, Finset.sum_insert has]
    refine Finset.Subset.trans
      (MvPolynomial.vars_add_subset _ _) (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    assumption

