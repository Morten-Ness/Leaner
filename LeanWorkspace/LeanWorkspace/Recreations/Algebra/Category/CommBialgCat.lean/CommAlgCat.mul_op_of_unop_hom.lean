import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem CommAlgCat.mul_op_of_unop_hom {A : Type u} [CommRing A] [Bialgebra R A] :
    μ[op <| CommAlgCat.of R A].unop.hom = comulAlgHom R A := rfl

