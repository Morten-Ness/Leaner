import Mathlib

theorem ofHom_apply {X Y : Type u} [Group X] [Group Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

-- This is essentially an alias for `Iso.hom_inv_id_apply`; consider deprecation?

