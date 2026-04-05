import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem mem_vars (i : σ) : i ∈ p.vars ↔ ∃ d ∈ p.support, i ∈ d.support := by
  classical simp only [MvPolynomial.vars_def, Multiset.mem_toFinset, mem_degrees, mem_support_iff]

