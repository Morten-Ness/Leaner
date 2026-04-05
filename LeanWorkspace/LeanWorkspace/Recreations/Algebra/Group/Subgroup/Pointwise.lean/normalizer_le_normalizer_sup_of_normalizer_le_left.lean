import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem normalizer_le_normalizer_sup_of_normalizer_le_left
    {H K : Subgroup G} (hHnK : normalizer H ≤ normalizer (K : Set G)) :
    normalizer H ≤ normalizer ((H ⊔ K : Subgroup G) : Set G) := (inf_of_le_left hHnK).symm.trans_le (H.normalizer_inf_normalizer_le_normalizer_sup K)

