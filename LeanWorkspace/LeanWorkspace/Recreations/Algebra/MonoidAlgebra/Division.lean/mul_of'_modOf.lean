import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

set_option backward.isDefEq.respectTransparency false in
theorem mul_of'_modOf (x : k[G]) (g : G) : x * of' k G g %ᵒᶠ g = 0 := by
  ext g'
  rw [Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [AddMonoidAlgebra.modOf_apply_self_add]
  · rw [AddMonoidAlgebra.modOf_apply_of_not_exists_add _ _ _ h, of'_apply, mul_single_apply_of_not_exists_add]
    simpa only [add_comm] using h

