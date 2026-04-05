import Mathlib

variable (R : Type u) [CommRing R]

theorem ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

