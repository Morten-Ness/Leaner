import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem inv_add_inv' (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ := let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b

