import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

theorem Matrix.toBilin'Aux_single [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n) :
    M.toBilin'Aux (Pi.single i 1) (Pi.single j 1) = M i j := Matrix.toLinearMap₂'Aux_single _ _ _ _ _

