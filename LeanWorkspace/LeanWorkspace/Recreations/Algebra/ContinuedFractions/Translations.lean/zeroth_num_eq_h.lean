import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_num_eq_h : g.nums 0 = g.h := rfl

