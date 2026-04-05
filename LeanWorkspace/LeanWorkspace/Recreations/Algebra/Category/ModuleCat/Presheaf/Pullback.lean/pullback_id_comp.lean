import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

variable [(pushforward.{v} φ).IsRightAdjoint]

theorem pullback_id_comp :
    PresheafOfModules.pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (PresheafOfModules.pullbackId S) (PresheafOfModules.pullback φ) ≪≫ Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)

