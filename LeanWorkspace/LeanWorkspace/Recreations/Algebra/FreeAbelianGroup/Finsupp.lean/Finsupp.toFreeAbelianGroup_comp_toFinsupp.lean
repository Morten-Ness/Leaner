import Mathlib

variable {X : Type*}

theorem Finsupp.toFreeAbelianGroup_comp_toFinsupp :
    toFreeAbelianGroup.comp toFinsupp = AddMonoidHom.id (FreeAbelianGroup X) := by
  ext
  rw [toFreeAbelianGroup, toFinsupp, AddMonoidHom.comp_apply, lift_apply_of,
    liftAddHom_apply_single, AddMonoidHom.flip_apply, smulAddHom_apply, one_smul,
    AddMonoidHom.id_apply]

