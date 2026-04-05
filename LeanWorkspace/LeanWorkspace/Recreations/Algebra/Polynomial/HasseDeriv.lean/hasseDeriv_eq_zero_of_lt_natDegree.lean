import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_eq_zero_of_lt_natDegree (p : R[X]) (n : ℕ) (h : p.natDegree < n) :
    Polynomial.hasseDeriv n p = 0 := by
  rw [Polynomial.hasseDeriv_apply, sum_def]
  refine Finset.sum_eq_zero fun x hx => ?_
  simp [Nat.choose_eq_zero_of_lt ((le_natDegree_of_mem_supp _ hx).trans_lt h)]

