import Mathlib

variable {α R M M₂ : Type*}

theorem map_inv_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*)
    [DivisionSemiring R] [DivisionSemiring S] [Module R M]
    [Module S M₂] (n : ℕ) (x : M) : f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  · simp [hR, hS, map_zero f]
  · suffices ∀ y, f y = 0 by rw [this, this, smul_zero]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x), ← map_natCast_smul f R S]
    simp [hR, map_zero f]
  · suffices ∀ y, f y = 0 by simp [this]
    clear x
    intro x
    rw [← smul_inv_smul₀ hR x, map_natCast_smul f R S, hS, zero_smul]
  · rw [← inv_smul_smul₀ hS (f _), ← map_natCast_smul f R S, smul_inv_smul₀ hR]

