import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem fromCoset_ne_of_nin_range {b : B} (hb : b ∉ f.hom.range) :
    fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ ≠ fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  intro r
  simp only [fromCoset.injEq, Subtype.mk.injEq] at r
  nth_rw 2 [show (f.hom.range : Set B) = (1 : B) • f.hom.range from (one_leftCoset _).symm] at r
  rw [leftCoset_eq_iff, mul_one] at r
  exact hb (inv_inv b ▸ Subgroup.inv_mem _ r)

