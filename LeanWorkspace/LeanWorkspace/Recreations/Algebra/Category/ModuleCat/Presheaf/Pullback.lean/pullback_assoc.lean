import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

variable [(pushforward.{v} φ).IsRightAdjoint]

variable [(pushforward.{v} ψ).IsRightAdjoint]

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')
  [(pushforward.{v} ψ').IsRightAdjoint]

theorem pullback_assoc :
    isoWhiskerLeft _ (PresheafOfModules.pullbackComp.{v} ψ ψ') ≪≫
      PresheafOfModules.pullbackComp.{v} (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (PresheafOfModules.pullbackComp.{v} φ ψ) _ ≪≫
        PresheafOfModules.pullbackComp.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ' :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

