import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    (f ≫ g).app X = f.app X ≫ g.app X := by
  rfl

