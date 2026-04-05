import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable (β) [One α] [Preorder α] {a : α}

variable {β} [Nonempty β]

theorem const_lt_one : const β a < 1 ↔ a < 1 := const_lt_const

