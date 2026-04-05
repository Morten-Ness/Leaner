import Mathlib

variable {K L : Type*}

variable [DivisionRing K] {a b c d : K}

theorem inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ := let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b

