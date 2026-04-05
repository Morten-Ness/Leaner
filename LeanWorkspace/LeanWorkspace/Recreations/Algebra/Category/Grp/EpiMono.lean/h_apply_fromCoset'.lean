import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_fromCoset' (x : B) (b : B) (hb : b ∈ f.hom.range) :
    GrpCat.SurjectiveOfEpiAuxs.h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ := (GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ hb).symm ▸ GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset f x

