import Mathlib

section

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

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pushforward_comp_id :
    PresheafOfModules.pushforwardComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerLeft (PresheafOfModules.pushforward.{v} φ) (PresheafOfModules.pushforwardId S) ≪≫ rightUnitor _ := by ext; rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pushforward_id_comp :
    PresheafOfModules.pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerRight (PresheafOfModules.pushforwardId R) (PresheafOfModules.pushforward.{v} φ) ≪≫ leftUnitor _ := by ext; rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pushforward_map_app_apply' {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_] ↑((ModuleCat.restrictScalars _).obj _))
      (((PresheafOfModules.pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable (F : C ⥤ D)

variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pushforward_obj_map_apply' (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_]
          ↑((ModuleCat.restrictScalars (S.map f).hom).obj ((ModuleCat.restrictScalars _).obj _)))
        (((PresheafOfModules.pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

end
