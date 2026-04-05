import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

variable [Fintype n] [Fintype n']

variable (b₁ : Basis n R M₁) (b₂ : Basis n' R M₂)

variable (J J₂ : Matrix n n R) (J' : Matrix n' n' R)

variable (A : Matrix n' n R) (A' : Matrix n n' R)

variable (A₁ A₂ : Matrix n n R)

variable [DecidableEq n] [DecidableEq n']

theorem isAdjointPair_toLinearMap₂ :
    LinearMap.IsAdjointPair (Matrix.toLinearMap₂ b₁ b₁ J)
      (Matrix.toLinearMap₂ b₂ b₂ J') (Matrix.toLin b₁ b₂ A) (Matrix.toLin b₂ b₁ A') ↔
      Matrix.IsAdjointPair J J' A A' := by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  have h :
    ∀ B B' : M₁ →ₗ[R] M₂ →ₗ[R] R,
      B = B' ↔ LinearMap.toMatrix₂ b₁ b₂ B = LinearMap.toMatrix₂ b₁ b₂ B' := by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (LinearMap.toMatrix₂ b₁ b₂).injective h
  simp_rw [h, LinearMap.toMatrix₂_comp b₂ b₂, LinearMap.toMatrix₂_compl₂ b₁ b₁,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix₂_toLinearMap₂]
  rfl

