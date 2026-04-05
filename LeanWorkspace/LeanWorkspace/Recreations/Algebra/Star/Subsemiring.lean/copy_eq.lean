import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S := SetLike.coe_injective hs

