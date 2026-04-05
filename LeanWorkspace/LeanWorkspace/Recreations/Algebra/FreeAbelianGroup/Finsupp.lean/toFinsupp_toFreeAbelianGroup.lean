import Mathlib

variable {X : Type*}

theorem toFinsupp_toFreeAbelianGroup (f : X →₀ ℤ) :
    FreeAbelianGroup.toFinsupp (Finsupp.toFreeAbelianGroup f) = f := by
  rw [← AddMonoidHom.comp_apply, toFinsupp_comp_toFreeAbelianGroup, AddMonoidHom.id_apply]

