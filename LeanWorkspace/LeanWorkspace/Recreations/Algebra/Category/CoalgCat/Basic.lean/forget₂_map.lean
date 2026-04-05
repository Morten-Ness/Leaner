import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_map (X Y : CoalgCat R) (f : X ⟶ Y) :
    (forget₂ (CoalgCat R) (ModuleCat R)).map f = ModuleCat.ofHom (f.toCoalgHom : X →ₗ[R] Y) := rfl

