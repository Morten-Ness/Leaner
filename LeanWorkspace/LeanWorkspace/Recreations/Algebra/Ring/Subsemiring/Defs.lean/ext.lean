import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem ext {S T : Subsemiring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

