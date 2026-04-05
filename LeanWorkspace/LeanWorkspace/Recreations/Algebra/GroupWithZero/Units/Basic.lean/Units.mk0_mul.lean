import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext; rfl

