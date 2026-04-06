FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (MonoidWithZeroHom.inl G₀ H₀ m) (MonoidWithZeroHom.inr G₀ H₀ n) := by
  rw [Commute, SemiconjBy]
  by_cases hm : m = 0
  · subst hm
    simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.inr]
  · by_cases hn : n = 0
    · subst hn
      simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.inr]
    · simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.inr, hm, hn, mul_comm]
