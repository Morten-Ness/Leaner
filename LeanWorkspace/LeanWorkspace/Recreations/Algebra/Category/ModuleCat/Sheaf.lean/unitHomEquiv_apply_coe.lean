import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

theorem unitHomEquiv_apply_coe (M : SheafOfModules R) (f : SheafOfModules.unit R ⟶ M) (X : Cᵒᵖ) :
    (M.unitHomEquiv f).val X = f.val.app X (1 : R.obj.obj X) := rfl

