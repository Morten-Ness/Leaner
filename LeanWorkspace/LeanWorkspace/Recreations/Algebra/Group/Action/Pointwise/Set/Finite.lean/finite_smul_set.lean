import Mathlib

open scoped Pointwise

variable {G α : Type*} [Group G] [MulAction G α] {a : G} {s : Set α}

theorem finite_smul_set : (a • s).Finite ↔ s.Finite := finite_image_iff (MulAction.injective _).injOn

