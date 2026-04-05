import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem OneHom.comp_one [One M] [One N] [One P] (f : OneHom N P) : f.comp (1 : OneHom M N) = 1 := by
  ext
  simp only [map_one, OneHom.coe_comp, Function.comp_apply, OneHom.one_apply]

