import Mathlib

theorem ofHom_apply {X Y : Type u} [Mul X] [Mul Y] (f : X →ₙ* Y) (x : X) :
    (ofHom f) x = f x := rfl

