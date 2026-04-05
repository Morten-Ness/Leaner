import Mathlib

variable {I α β γ : Type*}

variable {f : I → Type*}

variable (β) [One α] [Preorder α] {a : α}

theorem one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := fun _ => ha

