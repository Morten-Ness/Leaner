import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem map_eq_zero_iff : f x = 0 ↔ x = 0 := EmbeddingLike.map_eq_zero_iff

