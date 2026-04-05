import Mathlib

variable {R : Type u} [CommRing R]

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

theorem ofHom_comp (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

