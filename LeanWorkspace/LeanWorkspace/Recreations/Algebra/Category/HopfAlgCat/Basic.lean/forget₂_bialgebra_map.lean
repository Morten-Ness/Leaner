import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_bialgebra_map (X Y : HopfAlgCat R) (f : X ⟶ Y) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).map f = BialgCat.ofHom f.toBialgHom := rfl

