import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem Matrix.toBilin'_single (M : Matrix n n R₁) (i j : n) :
    Matrix.toBilin' M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [Matrix.toBilin'_apply, Pi.single_apply]

