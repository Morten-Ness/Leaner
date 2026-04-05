import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem iterate_map_div {M F : Type*} [Group M] [FunLike F M M] [MonoidHomClass F M M]
    (f : F) (n : ℕ) (x y : M) :
    f^[n] (x / y) = f^[n] x / f^[n] y := Semiconj₂.iterate (map_div f) n x y

