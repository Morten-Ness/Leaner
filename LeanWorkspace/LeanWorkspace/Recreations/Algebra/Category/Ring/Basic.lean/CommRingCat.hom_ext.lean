import Mathlib

theorem hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := Hom.ext hf

