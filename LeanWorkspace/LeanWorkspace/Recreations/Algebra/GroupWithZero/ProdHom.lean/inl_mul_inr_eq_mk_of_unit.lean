import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

theorem inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) :
    (MonoidWithZeroHom.inl G₀ H₀ m * MonoidWithZeroHom.inr G₀ H₀ n) = (m, n) := by
  simp [MonoidWithZeroHom.inl, WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.inr, ← WithZero.coe_mul]

