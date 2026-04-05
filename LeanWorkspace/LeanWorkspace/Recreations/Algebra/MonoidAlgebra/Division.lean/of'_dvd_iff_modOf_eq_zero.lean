import Mathlib

variable {k G : Type*} [Semiring k]

variable [AddCommMonoid G]

theorem of'_dvd_iff_modOf_eq_zero [IsCancelAdd G] {x : k[G]} {g : G} :
    of' k G g ∣ x ↔ x %ᵒᶠ g = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [AddMonoidAlgebra.of'_mul_modOf]
  · intro h
    rw [← AddMonoidAlgebra.divOf_add_modOf x g, h, add_zero]
    exact dvd_mul_right _ _

