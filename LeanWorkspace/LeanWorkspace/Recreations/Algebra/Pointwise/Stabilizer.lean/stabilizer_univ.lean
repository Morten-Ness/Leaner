import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_univ : stabilizer G (Set.univ : Set α) = ⊤ := by
  ext
  simp

