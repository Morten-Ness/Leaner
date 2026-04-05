import Mathlib

variable (R : Type u) [CommRing R]

theorem hom_ext {A B : AlgCat.{v} R} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g := Hom.ext hf

