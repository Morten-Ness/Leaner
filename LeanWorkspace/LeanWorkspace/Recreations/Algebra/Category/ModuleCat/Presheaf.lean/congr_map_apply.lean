import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

set_option backward.isDefEq.respectTransparency false in
theorem congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by rw [h]

