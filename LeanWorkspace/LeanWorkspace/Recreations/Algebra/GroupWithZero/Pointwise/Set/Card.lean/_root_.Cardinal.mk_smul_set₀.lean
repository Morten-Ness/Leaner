import Mathlib

open scoped Cardinal Pointwise

variable {G₀ M₀ : Type*}

variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

theorem _root_.Cardinal.mk_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : #↥(a • s) = #s := Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn

