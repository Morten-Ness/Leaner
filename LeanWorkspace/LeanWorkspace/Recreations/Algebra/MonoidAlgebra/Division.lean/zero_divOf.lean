import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0 := map_zero (Finsupp.comapDomain.addMonoidHom _)

