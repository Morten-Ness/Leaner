import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_conv_eq_h : g.convs 0 = g.h := by
  simp [GenContFract.conv_eq_num_div_den, GenContFract.num_eq_conts_a, GenContFract.den_eq_conts_b, div_one]

