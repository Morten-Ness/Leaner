import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_comap_eq (f : R →+* S) (t : Subsemiring S) : (t.comap f).map f = t ⊓ f.rangeS := SetLike.coe_injective Set.image_preimage_eq_inter_range

