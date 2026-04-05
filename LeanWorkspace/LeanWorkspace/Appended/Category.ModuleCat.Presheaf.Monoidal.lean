import Mathlib

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem leftUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).hom.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem rightUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).hom.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    dsimp% (f ⊗ₘ g).app X =
      MonoidalCategory.tensorHom (C := ModuleCat (R.obj X)) (f.app X) (g.app X) := rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in
theorem tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((PresheafOfModules.Monoidal.tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

end

section

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (M₁ M₂ M₃ M₄ : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

theorem whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

end
