import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [(pushforward.{u} φ).IsRightAdjoint]

theorem pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (SheafOfModules.pullbackObjUnitToUnit φ) =
      SheafOfModules.unitToPushforwardObjUnit φ := Equiv.apply_symm_apply _ _

