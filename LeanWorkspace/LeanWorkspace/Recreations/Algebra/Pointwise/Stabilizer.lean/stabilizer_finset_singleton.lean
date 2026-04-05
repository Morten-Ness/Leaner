import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem stabilizer_finset_singleton (b : α) : stabilizer G ({b} : Finset α) = stabilizer G b := by
  ext; simp

