import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem commute_inlₗ_inrₗ (m : α) (n : β) : Commute (OrderMonoidHom.inlₗ α β m) (OrderMonoidHom.inrₗ α β n) := Commute.prod (.one_right m) (.one_left n)

