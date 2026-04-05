import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem map_ne_one_iff : f x ≠ 1 ↔ x ≠ 1 := EmbeddingLike.map_ne_one_iff

