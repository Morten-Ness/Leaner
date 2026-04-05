import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card := card_image_of_injective _ <| MulAction.injective _

