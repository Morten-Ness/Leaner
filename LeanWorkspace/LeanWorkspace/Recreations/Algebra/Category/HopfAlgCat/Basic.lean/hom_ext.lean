import Mathlib

variable (R : Type u) [CommRing R]

theorem hom_ext {X Y : HopfAlgCat.{v} R} (f g : X ⟶ Y) (h : f.toBialgHom = g.toBialgHom) :
    f = g := Hom.ext h

