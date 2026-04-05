import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem τ_apply_fromCoset' (x : B) (hx : x ∈ f.hom.range) :
    τ (fromCoset ⟨x • ↑f.hom.range, ⟨x, rfl⟩⟩) = ∞ := (GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ hx).symm ▸ GrpCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset _

