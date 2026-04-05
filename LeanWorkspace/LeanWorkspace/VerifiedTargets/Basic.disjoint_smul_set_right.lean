import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  simpa using Set.disjoint_smul_set (a := a) (s := a⁻¹ • s)

