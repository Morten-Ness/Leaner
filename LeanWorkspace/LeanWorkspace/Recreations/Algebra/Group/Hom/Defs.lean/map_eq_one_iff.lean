import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [One M] [One N]

variable [FunLike F M N]

theorem map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Function.Injective f)
    {x : M} :
    f x = 1 ↔ x = 1 := hf.eq_iff' (map_one f)

