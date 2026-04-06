FAIL
import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  simpa [GenContFract.TerminatedAt] using g.s.terminatedAt_iff_get?_eq_none (n := n)
