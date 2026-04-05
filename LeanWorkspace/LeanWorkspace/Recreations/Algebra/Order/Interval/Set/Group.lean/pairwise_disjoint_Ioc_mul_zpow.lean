import Mathlib

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b : α)

theorem pairwise_disjoint_Ioc_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a * b ^ n) (a * b ^ (n + 1))) := by
  simp +unfoldPartialApp only [Function.onFun]
  simp_rw [Set.disjoint_iff]
  intro m n hmn x hx
  apply hmn
  have hb : 1 < b := by
    have : a * b ^ m < a * b ^ (m + 1) := hx.1.1.trans_le hx.1.2
    rwa [mul_lt_mul_iff_left, ← mul_one (b ^ m), zpow_add_one, mul_lt_mul_iff_left] at this
  have i1 := hx.1.1.trans_le hx.2.2
  have i2 := hx.2.1.trans_le hx.1.2
  rw [mul_lt_mul_iff_left, zpow_lt_zpow_iff_right hb, Int.lt_add_one_iff] at i1 i2
  exact le_antisymm i1 i2

