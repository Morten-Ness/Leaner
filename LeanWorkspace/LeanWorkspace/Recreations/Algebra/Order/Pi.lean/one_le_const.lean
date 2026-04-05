import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable (β) [One α] [Preorder α] {a : α}

variable {β} [Nonempty β]

theorem one_le_const : 1 ≤ const β a ↔ 1 ≤ a := const_le_const

