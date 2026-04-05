import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Group G] {s t : Set G}

variable [MulAction G α]

theorem ncard_smul_set (a : G) (s : Set α) : (a • s).ncard = s.ncard := by simp [ncard]

