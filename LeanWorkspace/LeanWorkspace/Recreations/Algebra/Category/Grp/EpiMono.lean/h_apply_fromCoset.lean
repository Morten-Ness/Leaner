import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_fromCoset (x : B) :
    (GrpCat.SurjectiveOfEpiAuxs.h x) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
      fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
  change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g x)).trans τ _ = _
  simp [-MonoidHom.coe_range, GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_fromCoset, GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity, GrpCat.SurjectiveOfEpiAuxs.τ_apply_infinity]

