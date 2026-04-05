import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable (β) [One α] [Preorder α] {a : α}

theorem const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := fun _ => ha

