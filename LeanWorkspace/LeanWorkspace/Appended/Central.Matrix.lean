import Mathlib

section

variable {n R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype n] [DecidableEq n]

theorem subalgebraCenter_eq_scalarAlgHom_map :
    Subalgebra.center R (Matrix n n A) = (Subalgebra.center R A).map (scalarAlgHom n R) := SetLike.coe_injective center_eq_scalar_image

end
