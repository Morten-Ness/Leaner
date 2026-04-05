import Mathlib

section

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Group G] {s t : Set G}

theorem natCard_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← Set.natCard_inv t]; exact Set.natCard_mul_le

end
