import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

theorem IsQuasicoherent.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsQuasicoherent (M.over (X i))] :
    IsQuasicoherent M := (QuasicoherentData.bind M X hX fun _ ↦
    IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

theorem Presentation.isQuasicoherent {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsQuasicoherent M where
  nonempty_quasicoherentData := Nonempty.intro (Presentation.quasicoherentData P)

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] {ι σ : Type u}

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable {M : SheafOfModules.{u} R} (P : Presentation M)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : F.obj (unit R) ≅ unit S)

theorem Presentation.mapRelations_mapGenerators :
    P.mapRelations F η ≫ P.mapGenerators F η = 0 := by
  simp only [mapRelations, mapGenerators, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] {ι σ : Type u}

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable {M : SheafOfModules.{u} R} (P : Presentation M)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : F.obj (unit R) ≅ unit S)

theorem Presentation.map_π_eq :
    (P.map F η).generators.π = (mapFree F η _).inv ≫ F.map (P.generators.π) := (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

end
