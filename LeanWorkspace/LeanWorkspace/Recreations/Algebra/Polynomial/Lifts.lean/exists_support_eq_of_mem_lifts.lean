import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem exists_support_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ Polynomial.lifts f) :
    ∃ q : R[X], map f q = p ∧ q.support = p.support := by
  rw [Polynomial.lifts_iff_coeff_lifts] at hlifts
  let g : ℕ → R := fun k ↦ (hlifts k).choose
  have hg : ∀ k, f (g k) = p.coeff k := fun k ↦ (hlifts k).choose_spec
  let q : R[X] := ∑ k ∈ p.support, monomial k (g k)
  have hq : map f q = p := by simp_rw [q, Polynomial.map_sum, map_monomial, hg, ← as_sum_support]
  have hq' : q.support = p.support := by
    simp_rw [Finset.ext_iff, mem_support_iff, q, finset_sum_coeff, coeff_monomial,
      Finset.sum_ite_eq', ite_ne_right_iff, mem_support_iff, and_iff_left_iff_imp, not_imp_not]
    exact fun k h ↦ by rw [← hg, h, map_zero]
  exact ⟨q, hq, hq'⟩

