import Mathlib

theorem hom_ofHom {X Y : Type u} [Semigroup X] [Semigroup Y] (f : X →ₙ* Y) : (ofHom f).hom = f := rfl

