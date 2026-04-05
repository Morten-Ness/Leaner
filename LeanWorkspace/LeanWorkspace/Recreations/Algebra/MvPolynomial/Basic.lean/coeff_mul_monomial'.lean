import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeff_mul_monomial' (m) (s : σ →₀ ℕ) (r : R) (p : MvPolynomial σ R) :
    MvPolynomial.coeff m (p * MvPolynomial.monomial s r) = if s ≤ m then MvPolynomial.coeff (m - s) p * r else 0 := by
  classical
  split_ifs with h
  · conv_rhs => rw [← MvPolynomial.coeff_mul_monomial _ s]
    rw [tsub_add_cancel_of_le h]
  · contrapose! h
    rw [← MvPolynomial.mem_support_iff] at h
    obtain ⟨j, -, rfl⟩ : ∃ j ∈ MvPolynomial.support p, j + s = m := by
      simpa [Finset.mem_add]
        using Finset.add_subset_add_left MvPolynomial.support_monomial_subset <| MvPolynomial.support_mul _ _ h
    exact le_add_left le_rfl

