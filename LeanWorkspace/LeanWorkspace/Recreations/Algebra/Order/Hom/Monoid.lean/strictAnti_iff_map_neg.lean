import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

variable [iamhc : AddMonoidHomClass F α β]

theorem strictAnti_iff_map_neg : StrictAnti (f : α → β) ↔ ∀ a, 0 < a → f a < 0 := strictMono_toDual_comp_iff.symm.trans <| strictMono_iff_map_pos (β := βᵒᵈ) (iamhc := iamhc) _

