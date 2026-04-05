import Mathlib

open scoped Pointwise symmDiff

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) := image_symmDiff (MulAction.injective a) _ _

