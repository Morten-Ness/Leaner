import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem ext {S T : StarSubsemiring R} (h : ∀ x : R, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

