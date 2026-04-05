import Mathlib

open scoped Pointwise symmDiff

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) := image_symmDiff _ _ <| MulAction.injective a

