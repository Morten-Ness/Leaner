import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem range_intCast : Set.range ((↑) : ℤ → R) = {0, 1} := by
  rw [funext CharTwo.intCast_eq_ite, Set.range_ite_const]
  · use 0; simp
  · use 1; simp

