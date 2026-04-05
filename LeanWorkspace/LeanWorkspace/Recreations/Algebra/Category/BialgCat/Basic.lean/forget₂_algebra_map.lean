import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_algebra_map (X Y : BialgCat R) (f : X ⟶ Y) :
    (forget₂ (BialgCat R) (AlgCat R)).map f = AlgCat.ofHom f.toBialgHom := rfl

