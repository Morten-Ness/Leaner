import Mathlib

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b : α)

theorem pairwise_disjoint_Ioo_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a * b ^ n) (a * b ^ (n + 1))) := fun _ _ hmn =>
  (Set.pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

