import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

theorem ofHom_apply (f : X →ₐc[R] Y) (x : X) : ofHom f x = f x := rfl

