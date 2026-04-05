import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

theorem ofHom_comp (f : X →ₐc[R] Y) (g : Y →ₐc[R] Z) : ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

