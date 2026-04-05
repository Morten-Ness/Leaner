import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Group G] {s t : Set G}

variable [MulAction G α]

theorem _root_.Cardinal.mk_smul_set (a : G) (s : Set α) : #↥(a • s) = #s := Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

