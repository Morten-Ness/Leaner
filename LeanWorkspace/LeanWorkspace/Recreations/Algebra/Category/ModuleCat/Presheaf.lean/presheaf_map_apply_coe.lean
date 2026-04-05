import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    DFunLike.coe (α := M.obj X) (β := fun _ ↦ M.obj Y) (M.presheaf.map f).hom x = M.map f x := rfl

