import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t := mem_image₂_of_mem

