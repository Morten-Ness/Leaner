import Mathlib

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

theorem equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero).hom := by
  have := limMap_π (diagramIsoParallelPair F).hom WalkingParallelPair.zero
  rw [← IsIso.comp_inv_eq] at this
  rw [← this]
  rw [← limit.isoLimitCone_hom_π
      ⟨_,
        CommRingCat.equalizerForkIsLimit (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)⟩
      WalkingParallelPair.zero]
  change IsLocalHom ((lim.map _ ≫ _ ≫ (CommRingCat.equalizerFork _ _).ι) ≫ _).hom
  infer_instance

