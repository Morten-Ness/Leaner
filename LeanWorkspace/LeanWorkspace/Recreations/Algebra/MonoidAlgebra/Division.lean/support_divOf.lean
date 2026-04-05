import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem support_divOf (g : G) (x : k[G]) :
    (x /ᵒᶠ g).support =
      x.support.preimage (g + ·) (Function.Injective.injOn (add_right_injective g)) := rfl

