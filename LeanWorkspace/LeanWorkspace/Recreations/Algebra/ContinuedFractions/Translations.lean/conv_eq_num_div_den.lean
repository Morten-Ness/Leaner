import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem conv_eq_num_div_den : g.convs n = g.nums n / g.dens n := rfl

