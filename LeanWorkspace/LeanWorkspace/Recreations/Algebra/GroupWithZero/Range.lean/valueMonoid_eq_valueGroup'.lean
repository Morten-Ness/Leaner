import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem valueMonoid_eq_valueGroup' : (MonoidWithZeroHom.valueMonoid f : Set Bˣ) = MonoidWithZeroHom.valueGroup f := by
  rw [valueMonoid_eq_valueGroup, coe_toSubmonoid]

