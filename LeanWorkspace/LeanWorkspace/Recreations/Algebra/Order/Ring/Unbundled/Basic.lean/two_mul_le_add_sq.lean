import Mathlib

variable {R : Type u} {α : Type*}

variable [CommSemiring R] [LinearOrder R] {a d : R}

theorem two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  simpa [fn_min_add_fn_max (fun x ↦ x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

