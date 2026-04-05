import Mathlib

theorem ofHom_apply {X Y : Type u} [CommMonoid X] [CommMonoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

