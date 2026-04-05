import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MulHom.map_mul [Mul M] [Mul N] (f : M →ₙ* N) (a b : M) : f (a * b) = f a * f b := f.map_mul' a b

