import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_ext {M N : SemimoduleCat.{v} R} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g := Hom.ext hf

