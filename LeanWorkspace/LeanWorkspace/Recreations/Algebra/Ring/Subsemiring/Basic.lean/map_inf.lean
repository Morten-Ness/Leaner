import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem map_inf (s t : Subsemiring R) (f : R →+* S) (hf : Function.Injective f) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter hf)

