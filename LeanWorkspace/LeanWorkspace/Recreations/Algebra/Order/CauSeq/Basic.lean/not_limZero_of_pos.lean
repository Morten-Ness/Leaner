import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem not_limZero_of_pos {f : CauSeq α abs} : CauSeq.Pos f → ¬CauSeq.LimZero f
  | ⟨_, F0, hF⟩, H =>
    let ⟨_, h⟩ := exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_ge h₁ (abs_lt.1 h₂).2

