import Mathlib

variable {α : Type*}

variable [Lattice α] [Group α]

variable [MulLeftMono α] [MulRightMono α]

theorem div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b := (OrderIso.divLeft c).map_sup _ _

