import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem inv_eq_self₀ {a : K} : a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  obtain rfl | ha := eq_or_ne a 0; · simp
  rw [← mul_eq_one_iff_inv_eq₀ ha, ← pow_two, sq_eq_one_iff]
  tauto

