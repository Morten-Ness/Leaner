import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

variable [IsCancelAdd G]

theorem divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b := by
  ext
  simp only [AddMonoidAlgebra.divOf_apply, add_assoc]

