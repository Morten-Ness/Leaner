import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

theorem smulRight_apply_eq_zero_iff [IsDomain S] {f : M₁ →ₗ[R] S} {x : M} [Module.IsTorsionFree S M] :
    f.smulRight x = 0 ↔ f = 0 ∨ x = 0 := by simp [DFunLike.ext_iff, forall_or_right]

