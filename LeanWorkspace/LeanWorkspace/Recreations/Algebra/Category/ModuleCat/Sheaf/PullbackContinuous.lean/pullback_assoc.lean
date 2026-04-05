import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [(pushforward.{v} φ).IsRightAdjoint]

variable {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

variable [(pushforward.{v} ψ).IsRightAdjoint]

variable {G' : D' ⥤ D''} {R'' : Sheaf K'' RingCat.{u}}
  [Functor.IsContinuous G' K' K'']
  [Functor.IsContinuous (G ⋙ G') K K'']
  [Functor.IsContinuous ((F ⋙ G) ⋙ G') J K'']
  [Functor.IsContinuous (F ⋙ G ⋙ G') J K'']
  (ψ' : R' ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K' K'').obj R'')

variable [(pushforward.{v} ψ').IsRightAdjoint]

theorem pullback_assoc :
    isoWhiskerLeft _ (SheafOfModules.pullbackComp.{v} ψ ψ') ≪≫
      SheafOfModules.pullbackComp.{v} (G := G ⋙ G') φ
        (ψ ≫ (G.sheafPushforwardContinuous RingCat.{u} K K').map ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (SheafOfModules.pullbackComp.{v} φ ψ) _ ≪≫
      SheafOfModules.pullbackComp.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ψ' :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

