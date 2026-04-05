import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem iterate_map_zpow {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) (k : ℤ) :
    f^[n] (x ^ k) = f^[n] x ^ k := Commute.iterate_left (map_zpow f · k) n x

