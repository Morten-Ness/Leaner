import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem normalizer_le_normalizer_sup_normal {H K : Subgroup G} [hK : K.Normal] :
    normalizer H ≤ normalizer ((H ⊔ K : Subgroup G) : Set G) := Subgroup.normalizer_le_normalizer_sup_of_normalizer_le_left le_normalizer_of_normal

