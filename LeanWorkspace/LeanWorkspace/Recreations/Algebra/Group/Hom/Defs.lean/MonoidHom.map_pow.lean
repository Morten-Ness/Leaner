import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.map_pow [Monoid M] [Monoid N] (f : M →* N) (a : M) (n : ℕ) :
    f (a ^ n) = f a ^ n := map_pow f a n

