import Mathlib

theorem ofHom_apply {X Y : Type u} [Monoid X] [Monoid Y] (f : X →* Y) (x : X) :
    (ofHom f) x = f x := rfl

