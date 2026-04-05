import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem fromCoset_eq_of_mem_range {b : B} (hb : b ∈ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ = fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  congr
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm]
  rw [leftCoset_eq_iff, mul_one]
  exact Subgroup.inv_mem _ hb

example (G : Type) [Group G] (S : Subgroup G) : Set G := S

