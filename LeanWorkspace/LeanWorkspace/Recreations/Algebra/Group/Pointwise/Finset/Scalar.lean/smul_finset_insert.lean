import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem smul_finset_insert (a : α) (b : β) (s : Finset β) : a • insert b s = insert (a • b) (a • s) := image_insert ..

