import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem coe_mul_of_right_le_normalizer_left (N H : Subgroup G) (hLE : H ≤ normalizer N) :
    (↑(N ⊔ H) : Set G) = N * H := by
  rw [← Subgroup.set_mul_normalizer_comm _ _ hLE, sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE]

