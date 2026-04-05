import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem normal_mul (N H : Subgroup G) [N.Normal] : (↑(N ⊔ H) : Set G) = N * H := Subgroup.coe_mul_of_right_le_normalizer_left N H le_normalizer_of_normal

