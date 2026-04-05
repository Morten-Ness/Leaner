import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

variable [iamhc : AddMonoidHomClass F α β]

theorem strictMono_iff_map_neg : StrictMono (f : α → β) ↔ ∀ a < 0, f a < 0 := strictAnti_comp_ofDual_iff.symm.trans <| strictAnti_iff_map_neg (α := αᵒᵈ) (iamhc := iamhc) _

