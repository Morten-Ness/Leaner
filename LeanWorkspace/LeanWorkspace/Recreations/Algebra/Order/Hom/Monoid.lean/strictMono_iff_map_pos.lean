import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

variable [iamhc : AddMonoidHomClass F α β]

theorem strictMono_iff_map_pos :
    StrictMono (f : α → β) ↔ ∀ a, 0 < a → 0 < f a := by
  refine ⟨fun h a => ?_, fun h a b hl => ?_⟩
  · rw [← map_zero f]
    apply h
  · rw [← sub_add_cancel b a, map_add f]
    exact lt_add_of_pos_left _ (h _ <| sub_pos.2 hl)

