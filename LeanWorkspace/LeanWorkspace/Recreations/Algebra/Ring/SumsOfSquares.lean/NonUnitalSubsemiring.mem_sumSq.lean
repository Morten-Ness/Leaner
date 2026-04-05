import Mathlib

variable {R : Type*}

variable {T : Type*} [NonUnitalCommSemiring T]

theorem mem_sumSq {s : T} : s ∈ NonUnitalSubsemiring.sumSq T ↔ IsSumSq s := by
  simp [← NonUnitalSubsemiring.mem_toAddSubmonoid]

