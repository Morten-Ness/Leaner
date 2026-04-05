import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using AddMonoidAlgebra.mul_of'_modOf (1 : k[G]) g

