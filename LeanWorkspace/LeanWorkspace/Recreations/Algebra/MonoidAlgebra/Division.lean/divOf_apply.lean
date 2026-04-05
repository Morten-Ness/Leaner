import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem divOf_apply (g : G) (x : k[G]) (g' : G) : (x /ᵒᶠ g) g' = x (g + g') := rfl

