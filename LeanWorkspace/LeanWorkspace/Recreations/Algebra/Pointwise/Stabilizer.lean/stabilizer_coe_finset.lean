import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem stabilizer_coe_finset (s : Finset α) : stabilizer G (s : Set α) = stabilizer G s := by
  ext; simp [← Finset.coe_inj]

