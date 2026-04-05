import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t := image_inter <| MulAction.injective a

