import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_module_map {X Y : AlgCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap := rfl

