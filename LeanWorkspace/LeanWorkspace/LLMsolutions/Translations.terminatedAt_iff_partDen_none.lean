FAIL
import Mathlib

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  simp [GenContFract.TerminatedAt, Seq.TerminatedAt]
