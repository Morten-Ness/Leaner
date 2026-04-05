import Mathlib

variable {R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K] {a b : K}

theorem ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉₊ < 2 * a := Nat.ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

