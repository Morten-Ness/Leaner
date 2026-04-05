import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem freeCofan_inj {I : Type u} (i : I) :
    (SheafOfModules.freeCofan (R := R) I).inj i = SheafOfModules.ιFree i := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem freeHomEquiv_freeMap :
    (SheafOfModules.freeHomEquiv _ (SheafOfModules.freeMap (R := R) f)) = freeSection.comp f :=
  (SheafOfModules.freeHomEquiv _).symm.injective (by simp; rfl)

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I → M.sections)
    (p : M ⟶ N) :
    M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun i ↦ sectionsMap p (s i)) := N.freeHomEquiv.injective (by ext; simp [SheafOfModules.freeHomEquiv_comp_apply])

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (I J : Type u)

theorem inl_freeSumIso_hom :
    coprod.inl ≫ (SheafOfModules.freeSumIso (R := R) I J).hom = SheafOfModules.freeMap Sum.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (SheafOfModules.free (R := R) I) (SheafOfModules.free J)) _ (.mk .left)

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable (I J : Type u)

theorem inr_freeSumIso_hom :
    coprod.inr ≫ (SheafOfModules.freeSumIso (R := R) I J).hom = SheafOfModules.freeMap Sum.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (SheafOfModules.free (R := R) I) (SheafOfModules.free J)) _ (.mk .right)

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J'.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  (η : F.obj (unit R) ≅ unit S) (I : Type u) (i : I)
  [PreservesColimitsOfShape (Discrete I) F]

theorem map_ιFree_mapFree_hom :
    F.map (SheafOfModules.ιFree i) ≫ (SheafOfModules.mapFree F η I).hom = η.hom ≫ SheafOfModules.ιFree i := by
  have : η.inv ≫ η.hom ≫ SheafOfModules.ιFree i = (η.inv ≫ F.map (SheafOfModules.ιFree i)) ≫ (SheafOfModules.mapFree F η I).hom := by
    simp [← SheafOfModules.ιFree_mapFree_inv]
  rw [← Iso.hom_inv_id_assoc η (η.hom ≫ SheafOfModules.ιFree i)]
  simp [this]

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (SheafOfModules.freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← SheafOfModules.freeHomEquiv_comp_apply]

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem sectionsMap_freeHomEquiv_symm_freeSection
    {M : SheafOfModules.{u} R} (f : I → M.sections) (i : I) :
    sectionsMap ((SheafOfModules.freeHomEquiv M).symm f) (freeSection i) = f i := by
  obtain ⟨f, rfl⟩ := (SheafOfModules.freeHomEquiv M).surjective f
  cat_disch

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem unitHomEquiv_symm_freeHomEquiv_apply
    {I : Type u} {M : SheafOfModules.{u} R} (f : SheafOfModules.free I ⟶ M) (i : I) :
    M.unitHomEquiv.symm (M.freeHomEquiv f i) = SheafOfModules.ιFree i ≫ f := by
  simp [SheafOfModules.freeHomEquiv]

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {I J : Type u} (f : I → J)

theorem ιFree_freeMap (i : I) :
    SheafOfModules.ιFree (R := R) i ≫ SheafOfModules.freeMap f = SheafOfModules.ιFree (f i) := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, SheafOfModules.freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Category.comp_id]

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J'.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  (η : F.obj (unit R) ≅ unit S) (I : Type u) (i : I)
  [PreservesColimitsOfShape (Discrete I) F]

set_option backward.isDefEq.respectTransparency false in
theorem ιFree_mapFree_inv :
    SheafOfModules.ιFree i ≫ (SheafOfModules.mapFree F η I).inv = η.inv ≫ F.map (SheafOfModules.ιFree i) := by
  simp [SheafOfModules.mapFree, ← SheafOfModules.freeCofan_inj, Cofan.inj]

end
