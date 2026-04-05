import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

theorem ext {S T : Subsemigroup M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

