import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem comp_one [MulOne M] [MulOneClass N] [MulOneClass P] (f : N →* P) :
    f.comp (1 : M →* N) = 1 := by
  ext
  simp only [map_one, coe_comp, Function.comp_apply, one_apply]

