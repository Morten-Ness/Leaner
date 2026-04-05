import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 := (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

-- see Note [lower instance priority]

