import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem vars_add_of_disjoint [DecidableEq σ] (h : Disjoint p.vars q.vars) :
    (p + q).vars = p.vars ∪ q.vars := by
  refine (MvPolynomial.vars_add_subset p q).antisymm fun x hx => ?_
  simp only [MvPolynomial.vars_def, Multiset.disjoint_toFinset] at h hx ⊢
  rwa [degrees_add_of_disjoint h, Multiset.toFinset_union]

