import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

theorem map_eq_one_iff (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 := EmbeddingLike.map_eq_one_iff

