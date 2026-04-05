import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem conv_eq_conts_a_div_conts_b :
    g.convs n = (g.conts n).a / (g.conts n).b := rfl

