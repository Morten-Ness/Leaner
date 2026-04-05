import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N]

theorem map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod = (l.map f).prod := (List.prod_hom l f).symm

