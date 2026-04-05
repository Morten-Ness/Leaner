import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} := image_singleton _ _

