import Mathlib

variable {X : Type*}

theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    FreeAbelianGroup.support (k • a) = FreeAbelianGroup.support a := by
  apply FreeAbelianGroup.support_zsmul k _ a
  exact mod_cast h

