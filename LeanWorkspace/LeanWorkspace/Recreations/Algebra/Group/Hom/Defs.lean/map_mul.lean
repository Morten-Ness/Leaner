import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Mul M] [Mul N]

variable [FunLike F M N]

theorem map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x * f y := MulHomClass.map_mul f x y

