import Mathlib

variable {X : Type*}

theorem Finsupp.toFreeAbelianGroup_toFinsupp {X} (x : FreeAbelianGroup X) :
    Finsupp.toFreeAbelianGroup (FreeAbelianGroup.toFinsupp x) = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.toFreeAbelianGroup_comp_toFinsupp, AddMonoidHom.id_apply]

