import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommSemiring R]

variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂]
  [Module R N₂]

variable {σ₁ : R →+* R} {σ₂ : R →+* R} [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

variable (b₁ : Basis n R M₁) (b₂ : Basis m R M₂)

theorem apply_eq_dotProduct_toMatrix₂_mulVec (B : M₁ →ₛₗ[σ₁] M₂ →ₛₗ[σ₂] R) (x : M₁) (y : M₂) :
    B x y = (σ₁ ∘ b₁.repr x) ⬝ᵥ (toMatrix₂ b₁ b₂ B) *ᵥ (σ₂ ∘ b₂.repr y) := by
  nth_rw 1 [← b₁.sum_repr x, ← b₂.sum_repr y]
  suffices ∑ j, ∑ i, σ₂ (b₂.repr y j) * σ₁ (b₁.repr x i) * B (b₁ i) (b₂ j) =
           ∑ i, ∑ j, σ₁ (b₁.repr x i) * σ₂ (b₂.repr y j) * B (b₁ i) (b₂ j) by
    simpa [dotProduct, Matrix.mulVec_eq_sum, Finset.mul_sum, -Module.Basis.sum_repr, ← mul_assoc]
  simp_rw [mul_comm (σ₂ _)]
  exact Finset.sum_comm

-- Not a `simp` lemma since `LinearMap.toMatrix₂` needs an extra argument

