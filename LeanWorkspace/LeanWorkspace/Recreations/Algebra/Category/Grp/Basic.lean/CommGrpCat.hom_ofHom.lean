import Mathlib

theorem hom_ofHom {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) : (ofHom f).hom = f := rfl

