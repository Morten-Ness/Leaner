import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [(pushforward.{v} φ).IsRightAdjoint]

theorem pullback_id_comp :
    SheafOfModules.pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (SheafOfModules.pullbackId S) (SheafOfModules.pullback φ) ≪≫ Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)

