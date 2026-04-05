import Mathlib

theorem ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) (x : X) :
    FiniteGrp.ofHom f x = f x := rfl

