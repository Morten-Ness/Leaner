import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom (s : Multiset M) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F) :
    (s.map f).prod = f s.prod := Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, map_coe, prod_coe]

