import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

theorem monotone_iff_map_nonneg [iamhc : AddMonoidHomClass F α β] :
    Monotone (f : α → β) ↔ ∀ a, 0 ≤ a → 0 ≤ f a := ⟨fun h a => by
    rw [← map_zero f]
    apply h, fun h a b hl => by
    rw [← sub_add_cancel b a, map_add f]
    exact le_add_of_nonneg_left (h _ <| sub_nonneg.2 hl)⟩

