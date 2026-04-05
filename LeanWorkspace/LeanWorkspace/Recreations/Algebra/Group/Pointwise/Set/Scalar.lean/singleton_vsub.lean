import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (b -ᵥ ·) '' t := image2_singleton_left

