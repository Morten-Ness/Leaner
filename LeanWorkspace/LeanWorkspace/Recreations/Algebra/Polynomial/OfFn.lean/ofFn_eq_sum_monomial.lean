import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

set_option backward.isDefEq.respectTransparency false in
theorem ofFn_eq_sum_monomial {n : ℕ} (v : Fin n → R) : Polynomial.ofFn n v =
    ∑ i : Fin n, monomial i (v i) := by
  by_cases h : n = 0
  · subst h
    simp [Polynomial.ofFn]
  · rw [as_sum_range' (Polynomial.ofFn n v) n <| Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v]
    simp [Finset.sum_range]

