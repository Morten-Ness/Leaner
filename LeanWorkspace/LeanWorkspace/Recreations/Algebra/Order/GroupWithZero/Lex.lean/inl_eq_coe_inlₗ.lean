import Mathlib

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

theorem inl_eq_coe_inlₗ {m : α} (hm : m ≠ 0) :
    inl α β m = OrderMonoidHom.inlₗ αˣ βˣ (Units.mk0 _ hm) := by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

