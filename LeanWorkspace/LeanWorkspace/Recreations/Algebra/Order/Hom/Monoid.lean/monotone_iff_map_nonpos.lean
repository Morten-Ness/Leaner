import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

variable [iamhc : AddMonoidHomClass F α β]

theorem monotone_iff_map_nonpos : Monotone (f : α → β) ↔ ∀ a ≤ 0, f a ≤ 0 := antitone_comp_ofDual_iff.symm.trans <| antitone_iff_map_nonpos (α := αᵒᵈ) (iamhc := iamhc) _

