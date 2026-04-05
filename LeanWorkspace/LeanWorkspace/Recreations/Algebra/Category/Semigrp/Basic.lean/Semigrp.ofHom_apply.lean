import Mathlib

theorem ofHom_apply {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

