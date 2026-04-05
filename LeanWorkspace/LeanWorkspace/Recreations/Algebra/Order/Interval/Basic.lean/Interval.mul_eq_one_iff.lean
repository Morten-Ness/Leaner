import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {s t : Interval α}

theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 := by
  cases s
  · simp
  cases t
  · simp
  · simp_rw [← NonemptyInterval.coe_mul_interval, ← NonemptyInterval.coe_one_interval,
      Interval.coe_inj, NonemptyInterval.coe_eq_pure]
    exact NonemptyInterval.mul_eq_one_iff

