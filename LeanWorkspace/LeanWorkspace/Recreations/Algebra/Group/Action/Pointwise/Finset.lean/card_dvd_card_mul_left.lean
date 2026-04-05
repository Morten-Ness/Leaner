import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

variable [DecidableEq α]

theorem card_dvd_card_mul_left {s t : Finset α} :
    ((fun b => s.image fun a => a * b) '' (t : Set α)).PairwiseDisjoint id →
      s.card ∣ (s * t).card := card_dvd_card_image₂_left fun _ _ => mul_left_injective _

