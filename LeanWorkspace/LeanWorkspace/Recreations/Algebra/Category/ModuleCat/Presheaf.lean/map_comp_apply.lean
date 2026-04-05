import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem map_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x) :
    M.map (i ≫ j) x = M.map j (M.map i x) := by
  rw [M.map_comp]; rfl

