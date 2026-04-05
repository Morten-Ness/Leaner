import Mathlib

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

theorem inr_eq_coe_inrₗ {n : β} (hn : n ≠ 0) :
    inr α β n = OrderMonoidHom.inrₗ αˣ βˣ (Units.mk0 _ hn) := by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp

