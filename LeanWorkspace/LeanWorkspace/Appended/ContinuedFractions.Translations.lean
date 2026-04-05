import Mathlib

section

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  rw [GenContFract.terminatedAt_iff_s_none, GenContFract.partDen_none_iff_s_none]

end

section

variable {α : Type*} {g : GenContFract α} {n : ℕ}

theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  rw [GenContFract.terminatedAt_iff_s_none, GenContFract.partNum_none_iff_s_none]

end

section

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_conv_eq_h : g.convs 0 = g.h := by
  simp [GenContFract.conv_eq_num_div_den, GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b, div_one]

end
