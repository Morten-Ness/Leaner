import Mathlib

theorem hom_ext {R S : RingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := Hom.ext hf

