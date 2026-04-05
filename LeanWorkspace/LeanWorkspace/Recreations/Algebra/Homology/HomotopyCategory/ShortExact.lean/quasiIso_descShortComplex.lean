import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

set_option backward.isDefEq.respectTransparency false in
include hS in
theorem quasiIso_descShortComplex : QuasiIso (CochainComplex.mappingCone.descShortComplex S) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _ ≫
          HomologicalComplex.homologyMap (CochainComplex.mappingCone.descShortComplex S) n)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
        (by
          erw [(homologyFunctorFactors C (up ℤ) n).hom.naturality_assoc]
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          rw [← HomologicalComplex.homologyMap_comp, CochainComplex.mappingCone.inr_descShortComplex])
        (by
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          erw [CochainComplex.mappingCone.homologySequenceδ_triangleh hS]
          simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj, assoc,
            Iso.inv_hom_id_app, comp_id])
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
    have : IsIso ((homologyFunctorFactors C (up ℤ) n).hom.app (CochainComplex.mappingCone S.f) ≫
        HomologicalComplex.homologyMap (CochainComplex.mappingCone.descShortComplex S) n) := by
      apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
        ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅_exact _
          (mappingCone_triangleh_distinguished S.f) n _ rfl).δlast
        (composableArrows₅_exact hS n _ rfl).δlast φ
      all_goals dsimp [φ]; infer_instance
    apply IsIso.of_isIso_comp_left ((homologyFunctorFactors C (up ℤ) n).hom.app (CochainComplex.mappingCone S.f))

