import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem modOf_apply_self_add (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g) (g + d) = 0 := AddMonoidAlgebra.modOf_apply_of_exists_add _ _ _ ⟨_, rfl⟩

