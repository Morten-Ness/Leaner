import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem _root_.map_multiset_prod [FunLike F M N] [MonoidHomClass F M N] (f : F) (s : Multiset M) :
    f s.prod = (s.map f).prod := (Multiset.prod_hom s f).symm

