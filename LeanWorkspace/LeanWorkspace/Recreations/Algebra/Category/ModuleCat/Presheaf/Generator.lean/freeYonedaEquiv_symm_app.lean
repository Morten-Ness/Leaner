import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

set_option backward.isDefEq.respectTransparency false in
theorem freeYonedaEquiv_symm_app (M : PresheafOfModules.{v} R) (X : C)
    (x : M.obj (Opposite.op X)) :
    (PresheafOfModules.freeYonedaEquiv.symm x).app (Opposite.op X) (ModuleCat.freeMk (𝟙 _)) = x := by
  dsimp [PresheafOfModules.freeYonedaEquiv, freeHomEquiv, yonedaEquiv]
  rw [ModuleCat.freeDesc_apply, op_id, M.presheaf.map_id]
  rfl

