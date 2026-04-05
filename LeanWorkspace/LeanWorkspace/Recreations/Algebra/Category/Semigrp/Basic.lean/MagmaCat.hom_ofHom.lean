import Mathlib

theorem hom_ofHom {M N : Type u} [Mul M] [Mul N] (f : M →ₙ* N) : (ofHom f).hom = f := rfl

