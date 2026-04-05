import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Group G] {s t : Set G}

variable [MulAction G α]

theorem encard_smul_set (a : G) (s : Set α) : (a • s).encard = s.encard := by
  simp [← toENat_cardinalMk]

