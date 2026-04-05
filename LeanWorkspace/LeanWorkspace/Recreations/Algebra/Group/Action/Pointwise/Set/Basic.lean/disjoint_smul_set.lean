import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Disjoint s t := disjoint_image_iff <| MulAction.injective _

