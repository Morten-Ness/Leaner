import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem mem_support_notMem_vars_zero {f : MvPolynomial σ R} {x : σ →₀ ℕ} (H : x ∈ f.support)
    {v : σ} (h : v ∉ MvPolynomial.vars f) : x v = 0 := by
  contrapose! h
  exact (MvPolynomial.mem_vars v).mpr ⟨x, H, Finsupp.mem_support_iff.mpr h⟩

