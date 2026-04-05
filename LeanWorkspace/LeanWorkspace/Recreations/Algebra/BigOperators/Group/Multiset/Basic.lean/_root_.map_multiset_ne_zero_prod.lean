import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem _root_.map_multiset_ne_zero_prod [FunLike F M N] [MulHomClass F M N] (f : F)
    {s : Multiset M} (hs : s ≠ 0) :
    f s.prod = (s.map f).prod := (Multiset.prod_hom_ne_zero s hs f).symm

