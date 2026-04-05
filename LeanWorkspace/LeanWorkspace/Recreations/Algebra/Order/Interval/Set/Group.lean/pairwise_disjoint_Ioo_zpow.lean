import Mathlib

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b : α)

theorem pairwise_disjoint_Ioo_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using Set.pairwise_disjoint_Ioo_mul_zpow 1 b

