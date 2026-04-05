import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable (β) [One α] [Preorder α] {a : α}

variable {β} [Nonempty β]

theorem one_lt_const : 1 < const β a ↔ 1 < a := const_lt_const

