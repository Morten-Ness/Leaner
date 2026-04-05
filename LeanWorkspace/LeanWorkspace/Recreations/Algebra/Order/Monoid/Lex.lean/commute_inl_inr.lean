import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem commute_inl_inr (m : α) (n : β) : Commute (OrderMonoidHom.inl α β m) (OrderMonoidHom.inr α β n) := Commute.prod (.one_right m) (.one_left n)

