import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem add_pos {f g : CauSeq α abs} : CauSeq.Pos f → CauSeq.Pos g → CauSeq.Pos (f + g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩

