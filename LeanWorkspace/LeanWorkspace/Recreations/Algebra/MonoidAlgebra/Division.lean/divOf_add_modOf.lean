import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

set_option backward.isDefEq.respectTransparency false in
theorem divOf_add_modOf [IsCancelAdd G] (x : k[G]) (g : G) :
    of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x := by
  ext g'
  rw [Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  swap
  · rw [AddMonoidAlgebra.modOf_apply_of_not_exists_add x _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h,
      zero_add]
  · rw [AddMonoidAlgebra.modOf_apply_self_add, add_zero]
    rw [of'_apply, single_mul_apply_aux, one_mul, AddMonoidAlgebra.divOf_apply]
    intro a ha
    exact add_right_inj _

