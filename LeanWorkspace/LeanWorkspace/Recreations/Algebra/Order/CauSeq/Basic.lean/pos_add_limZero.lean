import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem pos_add_limZero {f g : CauSeq α abs} : CauSeq.Pos f → CauSeq.LimZero g → CauSeq.Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := h j ij
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩

