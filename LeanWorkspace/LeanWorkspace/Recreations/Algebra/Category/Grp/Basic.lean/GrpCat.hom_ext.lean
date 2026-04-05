import Mathlib

theorem hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g := Hom.ext hf

