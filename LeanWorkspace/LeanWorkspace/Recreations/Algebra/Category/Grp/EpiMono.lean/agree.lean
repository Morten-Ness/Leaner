import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem agree : f.hom.range = { x | GrpCat.SurjectiveOfEpiAuxs.h x = GrpCat.SurjectiveOfEpiAuxs.g x } := by
  refine Set.ext fun b => ⟨?_, fun hb : GrpCat.SurjectiveOfEpiAuxs.h b = GrpCat.SurjectiveOfEpiAuxs.g b => by_contradiction fun r => ?_⟩
  · rintro ⟨a, rfl⟩
    change GrpCat.SurjectiveOfEpiAuxs.h (f a) = GrpCat.SurjectiveOfEpiAuxs.g (f a)
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩
    · rw [GrpCat.SurjectiveOfEpiAuxs.g_apply_fromCoset]
      by_cases m : y ∈ f.hom.range
      · rw [GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset' _ _ _ m, GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ m]
        change fromCoset _ = fromCoset ⟨f a • (y • _), _⟩
        simp only [← GrpCat.SurjectiveOfEpiAuxs.fromCoset_eq_of_mem_range _ (Subgroup.mul_mem _ ⟨a, rfl⟩ m), smul_smul]
      · rw [GrpCat.SurjectiveOfEpiAuxs.h_apply_fromCoset_nin_range f (f a) ⟨_, rfl⟩ _ m]
        simp only [leftCoset_assoc]
    · rw [GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity, GrpCat.SurjectiveOfEpiAuxs.h_apply_infinity f (f a) ⟨_, rfl⟩]
  · have eq1 : (GrpCat.SurjectiveOfEpiAuxs.h b) (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) =
        fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩ := by
      change ((τ).symm.trans (GrpCat.SurjectiveOfEpiAuxs.g b)).trans τ _ = _
      dsimp [GrpCat.SurjectiveOfEpiAuxs.tau]
      simp [GrpCat.SurjectiveOfEpiAuxs.g_apply_infinity f]
    have eq2 :
        GrpCat.SurjectiveOfEpiAuxs.g b (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = fromCoset ⟨b • ↑f.hom.range, b, rfl⟩ :=
      rfl
    exact (GrpCat.SurjectiveOfEpiAuxs.fromCoset_ne_of_nin_range _ r).symm (by rw [← eq1, ← eq2, DFunLike.congr_fun hb])

