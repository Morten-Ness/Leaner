import Mathlib

variable {F α β M N P G H : Type*}

variable [One M] [One N] [FunLike F M N] [EmbeddingLike F M N] [OneHomClass F M N]

theorem map_ne_one_iff {f : F} {x : M} :
    f x ≠ 1 ↔ x ≠ 1 := EmbeddingLike.map_eq_one_iff.not

