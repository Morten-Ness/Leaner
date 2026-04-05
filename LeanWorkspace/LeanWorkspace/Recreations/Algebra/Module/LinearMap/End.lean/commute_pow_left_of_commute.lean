import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

theorem commute_pow_left_of_commute
    [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
    {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc, ih,
    ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, Module.End.mul_eq_comp]

