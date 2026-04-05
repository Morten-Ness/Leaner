import Mathlib

theorem ofHom_apply {X Y : Type u} [CommGroup X] [CommGroup Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?

