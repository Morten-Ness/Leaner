import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem copy_eq (S : Subsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S := SetLike.coe_injective hs

