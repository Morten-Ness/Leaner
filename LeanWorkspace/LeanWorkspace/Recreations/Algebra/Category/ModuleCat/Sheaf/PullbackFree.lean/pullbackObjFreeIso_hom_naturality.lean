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

theorem pullbackObjFreeIso_hom_naturality {I J : Type u} (f : I → J) :
    (pullback φ).map (freeMap f) ≫ (SheafOfModules.pullbackObjFreeIso φ J).hom =
      (SheafOfModules.pullbackObjFreeIso φ I).hom ≫ freeMap f := Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i ↦ by simp [← Functor.map_comp_assoc])

