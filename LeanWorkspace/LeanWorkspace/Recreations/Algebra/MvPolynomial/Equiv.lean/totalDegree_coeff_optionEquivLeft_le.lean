import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem totalDegree_coeff_optionEquivLeft_le
    (p : MvPolynomial (Option S₁) R) (i : ℕ) :
    ((MvPolynomial.optionEquivLeft R S₁ p).coeff i).totalDegree ≤ p.totalDegree := by
  classical
  by_cases hpi : (MvPolynomial.optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree, Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain]
  · simpa [mem_support_iff, ← MvPolynomial.optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

