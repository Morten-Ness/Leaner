import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·) := image₂_singleton_left

