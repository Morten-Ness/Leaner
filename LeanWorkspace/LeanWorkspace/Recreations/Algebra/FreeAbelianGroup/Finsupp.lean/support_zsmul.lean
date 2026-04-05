import Mathlib

variable {X : Type*}

theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAbelianGroup X) :
    FreeAbelianGroup.support (k • a) = FreeAbelianGroup.support a := by
  ext x
  simp [h]

