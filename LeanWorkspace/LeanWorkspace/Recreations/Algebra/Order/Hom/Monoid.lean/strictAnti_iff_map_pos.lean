import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

variable [iamhc : AddMonoidHomClass F α β]

theorem strictAnti_iff_map_pos : StrictAnti (f : α → β) ↔ ∀ a < 0, 0 < f a := strictMono_comp_ofDual_iff.symm.trans <| strictMono_iff_map_pos (α := αᵒᵈ) (iamhc := iamhc) _

