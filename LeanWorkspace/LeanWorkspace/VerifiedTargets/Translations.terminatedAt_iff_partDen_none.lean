import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  rw [GenContFract.terminatedAt_iff_s_none, GenContFract.partDen_none_iff_s_none]

