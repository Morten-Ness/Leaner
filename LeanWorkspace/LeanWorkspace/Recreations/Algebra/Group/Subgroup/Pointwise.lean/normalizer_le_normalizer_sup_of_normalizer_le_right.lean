import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem normalizer_le_normalizer_sup_of_normalizer_le_right {H K : Subgroup G}
    (hHnK : normalizer H ≤ normalizer (K : Set G)) :
    normalizer H ≤ normalizer ((K ⊔ H : Subgroup G) : Set G) := by
  rw [sup_comm]
  exact Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_left hHnK

