import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem unit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : (PresheafOfModules.unit R).map f (1 : R.obj X) = (1 : R.obj Y) := (R.map f).hom.map_one

