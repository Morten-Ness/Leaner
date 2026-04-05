import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem ext {S T : Subring R} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

