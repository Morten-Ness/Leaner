import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.map_one [MulOne M] [MulOne N] (f : M →* N) : f 1 = 1 := f.map_one'

