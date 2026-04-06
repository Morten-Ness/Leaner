FAIL
import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) := by
  rcases eq_nat_or_neg n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simpa using (Commute.refl a).pow_right m
  · simpa [zpow_negSucc] using ((Commute.refl a).inv_right.pow_right (m + 1))
