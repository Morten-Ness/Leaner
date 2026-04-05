import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x : M) (k : ℕ) :
    f^[n] (x ^ k) = f^[n] x ^ k := Commute.iterate_left (map_pow f · k) n x

