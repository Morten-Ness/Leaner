import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R] [AddCommMonoid N₂] [Module R N₂] [Semiring R₁] [Semiring R₂]
  [Semiring S₁] [Semiring S₂] [Module S₁ N₂] [Module S₂ N₂]
  [SMulCommClass S₁ R N₂] [SMulCommClass S₂ R N₂] [SMulCommClass S₂ S₁ N₂]

variable {σ₁ : R₁ →+* S₁} {σ₂ : R₂ →+* S₂}

variable [Fintype n] [Fintype m]

variable [DecidableEq n] [DecidableEq m]

theorem Matrix.toLinearMap₂'_apply' {T : Type*} [CommSemiring T] (M : Matrix n m T) (v : n → T)
    (w : m → T) : Matrix.toLinearMap₂' T M v w = v ⬝ᵥ (M *ᵥ w) := by
  simp_rw [Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [smul_eq_mul, smul_eq_mul, mul_comm (w _), ← mul_assoc]

