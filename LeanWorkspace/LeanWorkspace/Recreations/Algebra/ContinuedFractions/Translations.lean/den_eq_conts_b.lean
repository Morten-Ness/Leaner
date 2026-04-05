import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem den_eq_conts_b : g.dens n = (g.conts n).b := rfl

