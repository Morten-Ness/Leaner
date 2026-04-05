import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_sdiff : a • (s \ t) = a • s \ a • t := image_sdiff _ _ <| MulAction.injective a

