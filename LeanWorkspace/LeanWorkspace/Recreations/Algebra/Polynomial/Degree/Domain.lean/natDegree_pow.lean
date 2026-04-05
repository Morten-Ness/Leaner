import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem natDegree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p := by
  classical
  obtain rfl | hp := eq_or_ne p 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  exact natDegree_pow' <| by
    rw [← leadingCoeff_pow, Ne, leadingCoeff_eq_zero]; exact pow_ne_zero _ hp

