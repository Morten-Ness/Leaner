import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R] [AddCommMonoid N₂] [Module R N₂] [Semiring R₁] [Semiring R₂]
  [Semiring S₁] [Semiring S₂] [Module S₁ N₂] [Module S₂ N₂]
  [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂] [SMulCommClass S₂ S₁ N₂]

variable {σ₁ : R₁ →+* S₁} {σ₂ : R₂ →+* S₂}

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

theorem Matrix.toLinearMapₛₗ₂'_apply (M : Matrix n m N₂) (x : n → R₁) (y : m → R₂) :
    -- porting note: we don't seem to have `∑ i j` as valid notation yet
    Matrix.toLinearMapₛₗ₂' R σ₁ σ₂ M x y = ∑ i, ∑ j, σ₁ (x i) • σ₂ (y j) • M i j := by
  rw [toLinearMapₛₗ₂', toMatrixₛₗ₂', LinearEquiv.coe_symm_mk, toLinearMap₂'Aux, mk₂'ₛₗ_apply]
  apply Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    rw [smul_comm]

