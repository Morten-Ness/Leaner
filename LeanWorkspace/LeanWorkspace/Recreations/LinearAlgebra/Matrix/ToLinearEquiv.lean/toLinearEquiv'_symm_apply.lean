import Mathlib

variable {n : Type*} [Fintype n]

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable [DecidableEq n]

theorem toLinearEquiv'_symm_apply (P : Matrix n n R) (h : Invertible P) :
    (↑(P.toLinearEquiv' h).symm : Module.End R (n → R)) = Matrix.toLin' (⅟P) := rfl

