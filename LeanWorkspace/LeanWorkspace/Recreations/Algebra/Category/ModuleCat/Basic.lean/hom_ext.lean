import Mathlib

variable (R : Type u) [Ring R]

theorem hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g := Hom.ext hf

