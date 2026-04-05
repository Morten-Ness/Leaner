import Mathlib

open scoped Pointwise

variable {G α : Type*} [Group G] [MulAction G α] {a : G} {s : Set α}

theorem infinite_smul_set : (a • s).Infinite ↔ s.Infinite := infinite_image_iff (MulAction.injective _).injOn

