import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  rw [GenContFract.terminatedAt_iff_s_none, GenContFract.partNum_none_iff_s_none]

