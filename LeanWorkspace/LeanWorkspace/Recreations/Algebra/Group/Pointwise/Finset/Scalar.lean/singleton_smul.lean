import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

theorem singleton_smul (a : α) : ({a} : Finset α) • t = a • t := image₂_singleton_left

