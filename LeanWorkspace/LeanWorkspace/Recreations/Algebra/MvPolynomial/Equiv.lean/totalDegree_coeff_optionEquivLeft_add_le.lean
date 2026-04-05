import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem totalDegree_coeff_optionEquivLeft_add_le
    (p : MvPolynomial (Option S₁) R) (i : ℕ) (hi : i ≤ p.totalDegree) :
    ((MvPolynomial.optionEquivLeft R S₁ p).coeff i).totalDegree + i ≤ p.totalDegree := by
  classical
  by_cases hpi : (MvPolynomial.optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree, add_comm, Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [mem_support_iff, ← MvPolynomial.optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

