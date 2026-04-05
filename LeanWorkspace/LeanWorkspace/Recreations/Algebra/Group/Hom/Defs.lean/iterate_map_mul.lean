import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [MulHomClass F M M]
    (f : F) (n : ℕ) (x y : M) :
    f^[n] (x * y) = f^[n] x * f^[n] y := Function.Semiconj₂.iterate (map_mul f) n x y

