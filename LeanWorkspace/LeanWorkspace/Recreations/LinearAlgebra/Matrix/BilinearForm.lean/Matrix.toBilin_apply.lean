import Mathlib

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable {n o : Type*}

variable [Fintype n] [Fintype o]

variable [DecidableEq n] (b : Basis n R₁ M₁)

theorem Matrix.toBilin_apply (M : Matrix n n R₁) (x y : M₁) :
    Matrix.toBilin b M x y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j := (Matrix.toLinearMap₂_apply _ _ _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

-- Not a `simp` lemma since `BilinForm.toMatrix` needs an extra argument

