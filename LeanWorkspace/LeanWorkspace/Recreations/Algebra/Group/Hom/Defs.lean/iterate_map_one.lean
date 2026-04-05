import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem iterate_map_one {M F : Type*} [One M] [FunLike F M M] [OneHomClass F M M]
    (f : F) (n : ℕ) :
    f^[n] 1 = 1 := iterate_fixed (map_one f) n

