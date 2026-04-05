import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem natDegree_hasseDeriv_le (p : R[X]) (n : ℕ) :
    natDegree (Polynomial.hasseDeriv n p) ≤ natDegree p - n := by
  classical
    rw [Polynomial.hasseDeriv_apply, sum_def]
    refine (natDegree_sum_le _ _).trans ?_
    simp_rw [Function.comp, natDegree_monomial]
    rw [Finset.fold_ite, Finset.fold_const]
    · simp only [ite_self, max_eq_right, zero_le', Finset.fold_max_le, true_and, and_imp,
        tsub_le_iff_right, mem_support_iff, Ne, Finset.mem_filter]
      intro x hx hx'
      have hxp : x ≤ p.natDegree := le_natDegree_of_ne_zero hx
      grind
    · simp

