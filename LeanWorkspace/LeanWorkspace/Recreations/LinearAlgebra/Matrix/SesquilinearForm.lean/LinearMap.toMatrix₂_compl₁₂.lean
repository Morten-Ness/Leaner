import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]

variable {σ₁ : R →+* R} {σ₂ : R →+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

variable [AddCommMonoid M₁'] [Module R M₁']

variable [AddCommMonoid M₂'] [Module R M₂']

variable (b₁' : Basis n' R M₁')

variable (b₂' : Basis m' R M₂')

variable [Fintype n'] [Fintype m']

variable [DecidableEq n'] [DecidableEq m']

theorem LinearMap.toMatrix₂_compl₁₂ (B : M₁ →ₗ[R] M₂ →ₗ[R] R) (l : M₁' →ₗ[R] M₁)
    (r : M₂' →ₗ[R] M₂) :
    LinearMap.toMatrix₂ b₁' b₂' (B.compl₁₂ l r) =
      (toMatrix b₁' b₁ l)ᵀ * LinearMap.toMatrix₂ b₁ b₂ B * toMatrix b₂' b₂ r := by
  ext i j
  simp only [LinearMap.toMatrix₂_apply, compl₁₂_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix_apply, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← LinearMap.sum_repr_mul_repr_mul b₁ b₂]
  rw [Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp

