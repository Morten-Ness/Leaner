import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

variable [(pushforward.{v} φ).IsRightAdjoint]

theorem pullback_comp_id :
    PresheafOfModules.pullbackComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerLeft _ (PresheafOfModules.pullbackId R) ≪≫ Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)

