import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

set_option backward.isDefEq.respectTransparency false in
theorem of'_mul_modOf (g : G) (x : k[G]) : of' k G g * x %ᵒᶠ g = 0 := by
  ext g'
  rw [Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [AddMonoidAlgebra.modOf_apply_self_add]
  · rw [AddMonoidAlgebra.modOf_apply_of_not_exists_add _ _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h]

