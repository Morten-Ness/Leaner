import Mathlib

variable (R : Type u) [Ring R]

theorem hom_ofHom {X Y : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] (f : X →ₗ[R] Y) : (ofHom f).hom = f := rfl

