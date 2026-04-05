import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem const_pos {x : α} : CauSeq.Pos (CauSeq.const x) ↔ 0 < x := ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩

