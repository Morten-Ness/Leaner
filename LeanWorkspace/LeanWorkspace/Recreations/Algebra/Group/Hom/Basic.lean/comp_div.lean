import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

theorem comp_div (f : G →* H) (g h : M →* G) : f.comp (g / h) = f.comp g / f.comp h := by
  ext
  simp

