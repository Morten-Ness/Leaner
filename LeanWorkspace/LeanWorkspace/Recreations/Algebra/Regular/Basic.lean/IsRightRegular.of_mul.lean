import Mathlib

variable {R : Type*}

variable [Semigroup R] {a b : R}

theorem IsRightRegular.of_mul (ab : IsRightRegular (b * a)) : IsRightRegular b := by
  refine fun x y xy => ab (?_ : x * (b * a) = y * (b * a))
  rw [← mul_assoc, ← mul_assoc]
  exact congr_arg (· * a) xy

