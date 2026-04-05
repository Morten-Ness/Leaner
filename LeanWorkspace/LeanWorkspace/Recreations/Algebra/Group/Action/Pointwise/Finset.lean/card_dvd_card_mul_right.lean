import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

variable [DecidableEq α]

theorem card_dvd_card_mul_right {s t : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s * t).card := card_dvd_card_image₂_right fun _ _ => mul_right_injective _

