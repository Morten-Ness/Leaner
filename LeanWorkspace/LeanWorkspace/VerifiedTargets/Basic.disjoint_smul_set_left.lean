import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  simpa using Set.disjoint_smul_set (a := a) (t := a⁻¹ • t)

