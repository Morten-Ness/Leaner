import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem num_eq_conts_a : g.nums n = (g.conts n).a := rfl

