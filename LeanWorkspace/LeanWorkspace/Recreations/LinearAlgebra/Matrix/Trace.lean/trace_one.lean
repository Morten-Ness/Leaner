import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq n] [AddCommMonoidWithOne R]

theorem trace_one : Matrix.trace (1 : Matrix n n R) = Fintype.card n := by
  simp_rw [Matrix.trace, diag_one, Pi.one_def, Finset.sum_const, nsmul_one, Finset.card_univ]

