import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_degree_lt {n : ℕ} (v : Fin n → R) : (Polynomial.ofFn n v).degree < n := by
  by_cases h : Polynomial.ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
      <| Polynomial.ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| Polynomial.ne_zero_of_ofFn_ne_zero h) _

