import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (f : F)
    (g : ι → M) : (s.map fun i => f <| g i).prod = f (s.map g).prod := by
  convert Multiset.prod_hom (s.map g) f
  exact (map_map _ _ _).symm

