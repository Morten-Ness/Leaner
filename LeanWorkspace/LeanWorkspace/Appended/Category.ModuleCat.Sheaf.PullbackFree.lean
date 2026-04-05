import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

theorem bijective_pushforwardSections [F.Final] :
    Function.Bijective (SheafOfModules.pushforwardSections φ (M := M)) :=
  Functor.bijective_sectionsPrecomp _ _

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [(pushforward.{u} φ).IsRightAdjoint]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

theorem pullbackObjFreeIso_hom_naturality {I J : Type u} (f : I → J) :
    (pullback φ).map (freeMap f) ≫ (SheafOfModules.pullbackObjFreeIso φ J).hom =
      (SheafOfModules.pullbackObjFreeIso φ I).hom ≫ freeMap f := Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i ↦ by simp [← Functor.map_comp_assoc])

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable [(pushforward.{u} φ).IsRightAdjoint]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

set_option backward.isDefEq.respectTransparency false in
theorem pullback_map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) :
    (pullback φ).map (ιFree i) ≫ (SheafOfModules.pullbackObjFreeIso φ I).hom =
      SheafOfModules.pullbackObjUnitToUnit φ ≫ ιFree i := by
  simp [SheafOfModules.pullbackObjFreeIso, ιFree]

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

set_option backward.isDefEq.respectTransparency false in
theorem pushforwardSections_unitHomEquiv
    {M : SheafOfModules.{u} R} (f : unit R ⟶ M) :
    SheafOfModules.pushforwardSections φ (M.unitHomEquiv f) =
      ((pushforward φ).obj M).unitHomEquiv
        (SheafOfModules.unitToPushforwardObjUnit φ ≫ (pushforward φ).map f) := by
  ext X
  have := SheafOfModules.unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  dsimp at this ⊢
  simp +instances [this, map_one]
  rfl

end
