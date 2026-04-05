import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

variable {n : ℕ}

theorem of_s_head (h : fract v ≠ 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩ := by
  change (of v).s.get? 0 = _
  rw [GenContFract.of_s_head_aux, GenContFract.IntFractPair.stream_succ_of_some (GenContFract.IntFractPair.stream_zero v) h, Option.bind]
  rfl

