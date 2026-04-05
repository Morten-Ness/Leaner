import Mathlib

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pullbackObjIsDefined_eq_top :
    pullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ ↦ PresheafOfModules.pullbackObjIsDefined_free_yoneda _ _)

end

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pullbackObjIsDefined_free_yoneda (X : C) :
    pullbackObjIsDefined φ ((free S).obj (yoneda.obj X)) := (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable

end

section

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

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

variable [(pushforward.{v} φ).IsRightAdjoint]

theorem pullback_comp_id :
    PresheafOfModules.pullbackComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerLeft _ (PresheafOfModules.pullbackId R) ≪≫ Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

variable [(pushforward.{v} φ).IsRightAdjoint]

theorem pullback_id_comp :
    PresheafOfModules.pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (PresheafOfModules.pullbackId S) (PresheafOfModules.pullback φ) ≪≫ Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)

end
