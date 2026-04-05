import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g := map_add (Finsupp.comapDomain.addMonoidHom _) _ _

