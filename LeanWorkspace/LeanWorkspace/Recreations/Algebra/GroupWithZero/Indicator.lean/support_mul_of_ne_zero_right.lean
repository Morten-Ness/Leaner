import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀]

theorem support_mul_of_ne_zero_right (f : ι → M₀) {g : ι → M₀} (hg : ∀ x, g x ≠ 0) :
    support (fun x => f x * g x) = support f := by simp [support_eq_univ hg]

