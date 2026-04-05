import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem g_ne_h (x : B) (hx : x ∉ f.hom.range) : GrpCat.SurjectiveOfEpiAuxs.g ≠ GrpCat.SurjectiveOfEpiAuxs.h := by
  intro r
  apply GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ hx
  replace r :=
    DFunLike.congr_fun (DFunLike.congr_fun r x) (fromCoset ⟨f.hom.range, ⟨1, one_leftCoset _⟩⟩)
  simpa [GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset, «GrpCat.SurjectiveOfEpiAuxs.h», GrpCat.SurjectiveOfEpiAuxs.tau, GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity] using r

