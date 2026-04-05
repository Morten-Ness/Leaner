import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem vars_add_subset [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p + q).vars ⊆ p.vars ∪ q.vars := by
  intro x hx
  simp only [MvPolynomial.vars_def, Finset.mem_union, Multiset.mem_toFinset] at hx ⊢
  simpa using Multiset.mem_of_le degrees_add_le hx

