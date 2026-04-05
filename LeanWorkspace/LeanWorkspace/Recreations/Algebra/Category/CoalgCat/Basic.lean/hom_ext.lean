import Mathlib

variable (R : Type u) [CommRing R]

theorem hom_ext {M N : CoalgCat.{v} R} (f g : M ⟶ N) (h : f.toCoalgHom = g.toCoalgHom) :
    f = g := Hom.ext h

