import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_infinity (x : B) (hx : x ∈ f.hom.range) : (GrpCat.SurjectiveOfEpiAuxs.h x) ∞ = ∞ := by
  change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g x)).trans τ _ = _
  simp only [Equiv.coe_trans, Function.comp_apply]
  rw [GrpCat.SurjectiveOfEpiAuxs.τ_symm_apply_infinity, GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset]
  simpa only using GrpCat.SurjectiveOfEpiAuxs.τ_apply_fromCoset' f x hx

