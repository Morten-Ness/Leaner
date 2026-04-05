import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem CommAlgCat.one_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    η[op <| CommAlgCat.of R A].unop.hom = counitAlgHom R A := rfl

