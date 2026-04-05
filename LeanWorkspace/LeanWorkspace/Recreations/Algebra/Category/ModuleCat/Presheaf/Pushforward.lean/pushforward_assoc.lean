import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

variable {T : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} (ψ : R ⟶ G.op ⋙ T)

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')

theorem pushforward_assoc :
    (PresheafOfModules.pushforward ψ').isoWhiskerLeft (PresheafOfModules.pushforwardComp φ ψ) ≪≫
      PresheafOfModules.pushforwardComp (F := F ⋙ G) (φ ≫ F.op.whiskerLeft ψ) ψ' =
    ((PresheafOfModules.pushforward ψ').associator (PresheafOfModules.pushforward ψ) (PresheafOfModules.pushforward φ)).symm ≪≫
      isoWhiskerRight (PresheafOfModules.pushforwardComp ψ ψ') (PresheafOfModules.pushforward φ) ≪≫
        PresheafOfModules.pushforwardComp (G := G ⋙ G') φ (ψ ≫ G.op.whiskerLeft ψ') := by ext; rfl

