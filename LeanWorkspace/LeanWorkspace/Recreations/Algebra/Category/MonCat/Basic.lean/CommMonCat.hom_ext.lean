import Mathlib

theorem hom_ext {M N : CommMonCat} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g := Hom.ext hf

