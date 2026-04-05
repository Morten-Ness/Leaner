import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]

variable {σ₁ : R →+* R} {σ₂ : R →+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

theorem dotProduct_toMatrix₂_mulVec (B : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] R) (x : n → R) (y : m → R) :
    (σ₁ ∘ x) ⬝ᵥ (toMatrix₂ b₁ b₂ B) *ᵥ (σ₂ ∘ y) =
      B (b₁.equivFun.symm x) (b₂.equivFun.symm y) := by
  simp only [dotProduct, Function.comp_apply, Function.comp_def, mulVec_eq_sum, op_smul_eq_smul,
    Finset.sum_apply, Pi.smul_apply, transpose_apply, toMatrix₂_apply, smul_eq_mul, mul_sum,
    Module.Basis.equivFun_symm_apply, map_sum, map_smulₛₗ, coe_sum, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  ring

