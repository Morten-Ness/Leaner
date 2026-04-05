import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem h_apply_fromCoset_nin_range (x : B) (hx : x ∈ f.hom.range) (b : B) (hb : b ∉ f.hom.range) :
    GrpCat.SurjectiveOfEpiAuxs.h x (fromCoset ⟨b • f.hom.range, b, rfl⟩) = fromCoset ⟨(x * b) • ↑f.hom.range, x * b, rfl⟩ := by
  change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g x)).trans τ _ = _
  simp only [GrpCat.SurjectiveOfEpiAuxs.tau, Equiv.coe_trans, Function.comp_apply]
  rw [Equiv.symm_swap,
    @Equiv.swap_apply_of_ne_of_ne X' _ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) ∞
      (fromCoset ⟨b • ↑f.hom.range, b, rfl⟩) (GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ hb) (by simp)]
  simp only [GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset, leftCoset_assoc]
  refine Equiv.swap_apply_of_ne_of_ne (GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ fun r => hb ?_) (by simp)
  convert Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) r
  rw [← mul_assoc, inv_mul_cancel, one_mul]

