import Mathlib

variable {m n : ℤ}

theorem natAbs_odd : Odd n.natAbs ↔ Odd n := by grind

protected alias ⟨_, _root_.Even.natAbs⟩ := natAbs_even
protected alias ⟨_, _root_.Odd.natAbs⟩ := natAbs_odd

