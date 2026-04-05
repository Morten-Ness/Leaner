import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] [DecidableEq o]

theorem Matrix.toBilin'_apply (M : Matrix n n R₁) (x y : n → R₁) :
    Matrix.toBilin' M x y = ∑ i, ∑ j, x i * M i j * y j := (Matrix.toLinearMap₂'_apply _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

