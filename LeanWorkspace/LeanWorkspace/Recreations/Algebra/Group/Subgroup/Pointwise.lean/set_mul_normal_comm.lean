import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem set_mul_normal_comm (S : Set G) (N : Subgroup G) [hN : N.Normal] :
    S * (N : Set G) = (N : Set G) * S := Subgroup.set_mul_normalizer_comm S N subset_normalizer_of_normal

