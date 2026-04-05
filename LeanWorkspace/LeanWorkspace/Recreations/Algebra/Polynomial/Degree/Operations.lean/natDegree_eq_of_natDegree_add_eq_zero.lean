import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_eq_of_natDegree_add_eq_zero (p q : R[X])
    (H : natDegree (p + q) = 0) : natDegree p = natDegree q := by
  by_cases h₁ : natDegree p = 0; on_goal 1 => by_cases h₂ : natDegree q = 0
  · exact h₁.trans h₂.symm
  · apply Polynomial.natDegree_eq_of_natDegree_add_lt_right; rwa [H, Nat.pos_iff_ne_zero]
  · apply Polynomial.natDegree_eq_of_natDegree_add_lt_left; rwa [H, Nat.pos_iff_ne_zero]

