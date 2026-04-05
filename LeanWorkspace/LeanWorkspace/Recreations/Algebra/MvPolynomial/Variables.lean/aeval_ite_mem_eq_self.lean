import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S]

theorem aeval_ite_mem_eq_self (q : MvPolynomial σ R) {s : Set σ} (hs : (q.vars : Set σ) ⊆ s)
    [∀ i, Decidable (i ∈ s)] :
    MvPolynomial.aeval (fun i ↦ if i ∈ s then .X i else 0) q = q := by
  rw [MvPolynomial.as_sum q, MvPolynomial.aeval_sum]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  exact Finsupp.prod_congr (fun i hi ↦ by simp [hs ((MvPolynomial.mem_vars _).mpr ⟨u, hu, hi⟩)])

