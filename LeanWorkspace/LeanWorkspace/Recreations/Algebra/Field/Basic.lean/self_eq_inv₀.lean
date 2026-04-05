import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem self_eq_inv₀ {a : K} : a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  rw [eq_comm, inv_eq_self₀]

-- see Note [lower instance priority]

