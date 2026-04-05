import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem mul_pos {f g : CauSeq α abs} : CauSeq.Pos f → CauSeq.Pos g → CauSeq.Pos (f * g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩

