import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

variable [DecidableEq α]

theorem stabilizer_finset_univ [Fintype α] : stabilizer G (Finset.univ : Finset α) = ⊤ := by
  ext
  simp

