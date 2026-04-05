import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [(pushforward.{u} φ).IsRightAdjoint]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

set_option backward.isDefEq.respectTransparency false in
theorem pullback_map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) :
    (pullback φ).map (ιFree i) ≫ (SheafOfModules.pullbackObjFreeIso φ I).hom =
      SheafOfModules.pullbackObjUnitToUnit φ ≫ ιFree i := by
  simp [SheafOfModules.pullbackObjFreeIso, ιFree]

