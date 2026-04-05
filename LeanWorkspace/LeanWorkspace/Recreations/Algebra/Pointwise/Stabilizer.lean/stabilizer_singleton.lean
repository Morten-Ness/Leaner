import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_singleton (b : α) : stabilizer G ({b} : Set α) = stabilizer G b := by ext; simp

