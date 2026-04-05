import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R) [Presheaf.IsLocallyInjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A)
  [Presheaf.IsLocallyInjective J φ] (hA : Presheaf.IsSeparated J A)
  {X : C} (r : R.obj (Opposite.op X)) (m : A.obj (Opposite.op X)) {P : Presieve X}
  (r₀ : FamilyOfElements (R₀ ⋙ forget _) P) (m₀ : FamilyOfElements (M₀.presheaf ⋙ forget _) P)

variable (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
  (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)

include hr₀ hm₀ in
theorem isCompatible_map_smul : ((r₀.smul m₀).map (whiskerRight φ (forget _))).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  let a₁ := r₀ f₁ h₁
  let b₁ := m₀ f₁ h₁
  let a₂ := r₀ f₂ h₂
  let b₂ := m₀ f₂ h₂
  let a₀ := R₀.map g₁.op a₁
  let b₀ := M₀.map g₁.op b₁
  have ha₁ : (α.app (Opposite.op Y₁)) a₁ = (R.map f₁.op) r := (hr₀ f₁ h₁).symm
  have ha₂ : (α.app (Opposite.op Y₂)) a₂ = (R.map f₂.op) r := (hr₀ f₂ h₂).symm
  have hb₁ : (φ.app (Opposite.op Y₁)) b₁ = (A.map f₁.op) m := (hm₀ f₁ h₁).symm
  have hb₂ : (φ.app (Opposite.op Y₂)) b₂ = (A.map f₂.op) m := (hm₀ f₂ h₂).symm
  have ha₀ : (α.app (Opposite.op Z)) a₀ = (R.map (f₁.op ≫ g₁.op)) r := by
    rw [← RingCat.comp_apply, NatTrans.naturality, RingCat.comp_apply, ha₁, Functor.map_comp,
      RingCat.comp_apply]
  have hb₀ : (φ.app (Opposite.op Z)) b₀ = (A.map (f₁.op ≫ g₁.op)) m := by
    dsimp [b₀]
    erw [NatTrans.naturality_apply φ, hb₁, Functor.map_comp, ConcreteCategory.comp_apply]
  have ha₀' : (α.app (Opposite.op Z)) a₀ = (R.map (f₂.op ≫ g₂.op)) r := by
    rw [ha₀, ← op_comp, fac, op_comp]
  have hb₀' : (φ.app (Opposite.op Z)) b₀ = (A.map (f₂.op ≫ g₂.op)) m := by
    rw [hb₀, ← op_comp, fac, op_comp]
  dsimp
  erw [← NatTrans.naturality_apply φ, ← NatTrans.naturality_apply φ]
  exact (CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul_aux α φ hA r m f₁ g₁ a₁ a₀ b₁ b₀ ha₁ ha₀ hb₁ hb₀).trans
    (CategoryTheory.Presieve.FamilyOfElements.isCompatible_map_smul_aux α φ hA r m f₂ g₂ a₂ a₀ b₂ b₀ ha₂ ha₀' hb₂ hb₀').symm

