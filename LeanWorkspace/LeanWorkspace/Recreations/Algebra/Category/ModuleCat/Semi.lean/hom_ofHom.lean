import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_ofHom {X Y : Type v} [AddCommMonoid X] [Module R X] [AddCommMonoid Y]
    [Module R Y] (f : X →ₗ[R] Y) : (ofHom f).hom = f := rfl

