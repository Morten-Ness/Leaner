import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.map_one [One M] [One N] (f : OneHom M N) : f 1 = 1 := f.map_one'

