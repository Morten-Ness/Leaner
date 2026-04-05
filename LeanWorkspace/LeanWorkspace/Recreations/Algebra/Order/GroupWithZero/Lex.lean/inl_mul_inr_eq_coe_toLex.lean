import Mathlib

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

theorem inl_mul_inr_eq_coe_toLex {m : α} {n : β} (hm : m ≠ 0) (hn : n ≠ 0) :
    inl α β m * inr α β n = toLex (Units.mk0 _ hm, Units.mk0 _ hn) := by
  rw [LinearOrderedCommGroupWithZero.inl_eq_coe_inlₗ hm, LinearOrderedCommGroupWithZero.inr_eq_coe_inrₗ hn,
      ← WithZero.coe_mul, OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

