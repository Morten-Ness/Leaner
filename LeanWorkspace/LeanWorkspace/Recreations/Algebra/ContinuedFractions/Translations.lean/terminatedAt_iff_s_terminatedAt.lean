import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl

