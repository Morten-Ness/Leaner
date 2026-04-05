import Mathlib

variable {F α β γ δ : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [i : FunLike F α β]

variable (f : F)

variable [iamhc : AddMonoidHomClass F α β]

theorem antitone_iff_map_nonpos : Antitone (f : α → β) ↔ ∀ a, 0 ≤ a → f a ≤ 0 := monotone_toDual_comp_iff.symm.trans <| monotone_iff_map_nonneg (β := βᵒᵈ) (iamhc := iamhc) _

