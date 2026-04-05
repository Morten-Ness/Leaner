import Mathlib

theorem hom_ext {R S : CommSemiRingCat} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := Hom.ext hf

