import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

variable (M : Cᵒᵖ ⥤ Ab.{v}) [∀ X, Module (R.obj X) (M.obj X)]
  (map_smul : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r : R.obj X) (m : M.obj X),
    M.map f (r • m) = R.map f r • M.map f m)

theorem ofPresheaf_presheaf : (PresheafOfModules.ofPresheaf M map_smul).presheaf = M := rfl

