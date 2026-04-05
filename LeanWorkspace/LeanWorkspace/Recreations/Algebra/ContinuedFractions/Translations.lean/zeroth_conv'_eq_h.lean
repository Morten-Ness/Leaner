import Mathlib

variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

theorem zeroth_conv'_eq_h : g.convs' 0 = g.h := by simp [convs']

