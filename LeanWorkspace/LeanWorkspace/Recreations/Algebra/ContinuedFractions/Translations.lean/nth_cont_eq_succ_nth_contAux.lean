import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem nth_cont_eq_succ_nth_contAux : g.conts n = g.contsAux (n + 1) := rfl

