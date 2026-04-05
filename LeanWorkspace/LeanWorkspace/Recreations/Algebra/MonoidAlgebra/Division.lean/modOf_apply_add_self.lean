import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem modOf_apply_add_self (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g) (d + g) = 0 := AddMonoidAlgebra.modOf_apply_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

