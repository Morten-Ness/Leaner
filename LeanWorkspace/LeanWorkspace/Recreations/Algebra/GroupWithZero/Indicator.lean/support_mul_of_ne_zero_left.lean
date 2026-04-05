import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀]

theorem support_mul_of_ne_zero_left {f : ι → M₀} (hf : ∀ x, f x ≠ 0) (g : ι → M₀) :
    support (fun x => f x * g x) = support g := by simp [support_eq_univ hf]

