import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by rfl

