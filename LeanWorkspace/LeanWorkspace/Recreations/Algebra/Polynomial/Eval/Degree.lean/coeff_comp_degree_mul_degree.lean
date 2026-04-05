import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_comp_degree_mul_degree (hqd0 : natDegree q ≠ 0) :
    coeff (p.comp q) (natDegree p * natDegree q) =
    leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [comp, eval₂_def, coeff_sum]
  refine Eq.trans (Finset.sum_eq_single p.natDegree ?h₀ ?h₁) ?h₂
  case h₂ =>
    simp only [coeff_natDegree, coeff_C_mul, coeff_pow_mul_natDegree]
  case h₀ =>
    intro b hbs hbp
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)
    rw [natDegree_C, zero_add]
    refine natDegree_pow_le.trans_lt ?_
    gcongr
    exact lt_of_le_of_ne (le_natDegree_of_mem_supp _ hbs) hbp
  case h₁ =>
    simp +contextual

