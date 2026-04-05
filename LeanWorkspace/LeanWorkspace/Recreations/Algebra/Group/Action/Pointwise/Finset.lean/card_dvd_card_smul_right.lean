import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem card_dvd_card_smul_right {s : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s • t).card := card_dvd_card_image₂_right fun _ _ => MulAction.injective _

