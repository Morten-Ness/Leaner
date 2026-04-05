import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem modOf_add_divOf [IsCancelAdd G] (x : k[G]) (g : G) :
    x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x := by
  rw [add_comm, AddMonoidAlgebra.divOf_add_modOf]

