import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem mul_normal (H N : Subgroup G) [hN : N.Normal] : (↑(H ⊔ N) : Set G) = H * N := Subgroup.coe_mul_of_left_le_normalizer_right H N le_normalizer_of_normal

