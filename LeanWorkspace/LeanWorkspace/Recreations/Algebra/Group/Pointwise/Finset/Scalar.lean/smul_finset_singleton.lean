import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} := image_singleton ..

