import Mathlib

variable {G M A B α β : Type*}

variable [Group α] [MulAction α β]

theorem smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y := (MulAction.injective g).eq_iff

