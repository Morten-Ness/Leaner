import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty := Nonempty.of_image₂_left

