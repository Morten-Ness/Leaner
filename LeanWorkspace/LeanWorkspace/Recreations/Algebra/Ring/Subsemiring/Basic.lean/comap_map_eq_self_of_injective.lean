import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem comap_map_eq_self_of_injective
    {f : R →+* S} (hf : Function.Injective f) (s : Subsemiring R) : (s.map f).comap f = s := SetLike.coe_injective (Set.preimage_image_eq _ hf)

