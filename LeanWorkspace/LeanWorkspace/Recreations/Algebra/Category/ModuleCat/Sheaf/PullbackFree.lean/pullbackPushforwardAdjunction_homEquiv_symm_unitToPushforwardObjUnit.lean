import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [(pushforward.{u} φ).IsRightAdjoint]

theorem pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit :
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (SheafOfModules.unitToPushforwardObjUnit φ) =
      SheafOfModules.pullbackObjUnitToUnit φ := rfl

