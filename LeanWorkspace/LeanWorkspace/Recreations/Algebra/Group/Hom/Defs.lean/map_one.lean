import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [One M] [One N]

variable [FunLike F M N]

theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 := OneHomClass.map_one f

