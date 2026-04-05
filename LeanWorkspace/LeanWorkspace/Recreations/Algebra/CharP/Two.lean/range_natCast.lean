import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem range_natCast : Set.range ((↑) : ℕ → R) = {0, 1} := by
  rw [funext CharTwo.natCast_eq_ite, Set.range_ite_const]
  · use 0; simp
  · use 1; simp

