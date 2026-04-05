import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

