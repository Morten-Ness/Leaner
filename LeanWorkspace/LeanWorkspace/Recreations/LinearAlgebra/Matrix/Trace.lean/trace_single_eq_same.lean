import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable {l m n : Type*} {R α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Fintype n] [AddCommMonoid α] (i j : n) (c : α)

theorem trace_single_eq_same : Matrix.trace (single i i c) = c := by
  simp [Matrix.trace]

