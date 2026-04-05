import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem naturality_apply (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    Hom.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x) := CategoryTheory.congr_fun (Hom.naturality f g) x

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    DFunLike.coe (α := M.obj X) (β := fun _ ↦ M.obj Y) (M.presheaf.map f).hom x = M.map f x := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem toPresheaf_map_app_apply (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X) :
    DFunLike.coe (α := M₁.obj X) (β := fun _ ↦ M₂.obj X)
      (((PresheafOfModules.toPresheaf R).map f).app X).hom x = f.app X x := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem zsmul_app (n : ℤ) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X := by
  ext x
  change (PresheafOfModules.toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

end
