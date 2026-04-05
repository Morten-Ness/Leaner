import Mathlib

open scoped IsMulCommutative

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

set_option backward.isDefEq.respectTransparency false in
theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (Algebra.adjoin R s).map φ = Algebra.adjoin R (φ '' s) := (Algebra.adjoin_image _ _ _).symm

